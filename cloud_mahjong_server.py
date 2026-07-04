import argparse, json, os, random, secrets, string, threading, time
from dataclasses import dataclass, field
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

TILE_NAMES=[f"{n}{s}" for s in ("万","筒","条") for n in range(1,10)]+["东","南","西","北","中","发","白"]
DEFAULT_NAMES=["南家","下家","对家","上家"]
TURN_SECONDS=30

def counts(tiles):
    c=[0]*34
    for t in tiles:c[t]+=1
    return c

def can_win_simple(hand,wild):
    # 轻量胡牌判断：保留自摸体验，允许龙牌补缺；后续可继续细化番型。
    return len(hand)%3==2 and (hand.count(wild)>=2 or any(v>=2 for v in counts(hand))) and len(hand)>=14

@dataclass
class Player:
    name:str
    human:bool=False
    token:str=""
    ready:bool=False
    hand:list=field(default_factory=list)
    discards:list=field(default_factory=list)
    score:int=0

class Room:
    def __init__(self,rid):
        self.room_id=rid; self.lock=threading.RLock(); self.players=[Player(DEFAULT_NAMES[i]) for i in range(4)]
        self.owner=None; self.phase='lobby'; self.wall=[]; self.dragon=0; self.current=0; self.dealer=0; self.must_discard=False; self.turn_at=time.time(); self.log=[]; self.round_no=1
        self.last_discard=None; self.last_discarder=None; self.awaiting_claim=False
        self.add_log('房间已创建。所有真人准备后，由房主开始游戏。')
    def add_log(self,x): self.log=(self.log+[x])[-100:]
    def humans(self): return [i for i,p in enumerate(self.players) if p.human]
    def all_ready(self):
        hs=self.humans(); return bool(hs) and all(self.players[i].ready for i in hs)
    def auth(self,seat,token): return 0<=seat<4 and self.players[seat].human and self.players[seat].token==token
    def join(self,name,token=''):
        with self.lock:
            if token:
                for i,p in enumerate(self.players):
                    if p.human and p.token==token:return i,p.token
            for i,p in enumerate(self.players):
                if not p.human:
                    p.human=True; p.ready=False; p.name=(name[:10] or f'玩家{i+1}'); p.token=secrets.token_urlsafe(12)
                    if self.owner is None:self.owner=i; self.add_log(f'{p.name} 加入房间，成为房主。')
                    else:self.add_log(f'{p.name} 加入房间。')
                    return i,p.token
            raise ValueError('房间已满')
    def ready(self,seat):
        with self.lock:
            if self.phase=='lobby': self.players[seat].ready=not self.players[seat].ready; self.add_log(f"{self.players[seat].name}{'已准备' if self.players[seat].ready else '取消准备'}。")
    def leave(self,seat):
        with self.lock:
            p=self.players[seat]
            if not p.human:return
            old=p.name; p.human=False; p.ready=False; p.token=''; p.name=DEFAULT_NAMES[seat]+'（电脑）'
            if self.owner==seat:
                hs=self.humans(); self.owner=hs[0] if hs else None
            self.add_log(f'{old} 退出，当前位置由电脑托管。')
            if self.phase=='playing' and self.current==seat:self.must_discard=False
        self.ai_until_human()
    def start(self,seat):
        with self.lock:
            if seat!=self.owner: raise ValueError('只有房主可以开始')
            if self.phase!='lobby': return
            if not self.all_ready(): raise ValueError('还有真人玩家未准备')
            old=[(p.name,p.human,p.token,p.ready,p.score) for p in self.players]
            self.players=[Player(n,h,t,r,score=s) for n,h,t,r,s in old]
            for i,p in enumerate(self.players):
                if not p.human:p.name=DEFAULT_NAMES[i]+'（电脑）'
            self.wall=list(range(34))*4; random.shuffle(self.wall); self.dragon=random.randrange(34); self.current=self.dealer
            self.last_discard=None; self.last_discarder=None; self.awaiting_claim=False
            for _ in range(13):
                for p in self.players:p.hand.append(self.wall.pop())
            self.players[self.dealer].hand.append(self.wall.pop())
            for p in self.players:p.hand.sort()
            self.phase='playing'; self.must_discard=True; self.turn_at=time.time(); self.add_log(f'第 {self.round_no} 局开始，庄家 {self.players[self.dealer].name}，龙牌 {TILE_NAMES[self.dragon]}。'); self.round_no+=1
        self.ai_until_human()
    def end_round(self,msg):
        self.add_log(msg); self.phase='lobby'; self.must_discard=False; self.awaiting_claim=False
        for p in self.players:
            if p.human:p.ready=False
            p.hand=[]; p.discards=[]
        self.add_log('本局结束，请所有真人重新准备，房主再开始下一局。')
    def draw(self,seat):
        if not self.wall:self.dealer=(self.dealer+1)%4; self.end_round('牌墙摸完，流局。'); return
        self.players[seat].hand.append(self.wall.pop()); self.players[seat].hand.sort(); self.turn_at=time.time()
    def ai_pick(self,p):
        pool=[t for t in p.hand if t!=self.dragon] or p.hand[:]
        c=counts(p.hand); pool.sort(key=lambda t:(c[t],random.random())); return pool[0]
    def timeout(self):
        if self.phase!='playing' or self.awaiting_claim or not self.players[self.current].human:return
        if time.time()-self.turn_at<TURN_SECONDS:return
        self.add_log(f'{self.players[self.current].name} 超时，系统自动托管。'); self.auto_discard(self.current)
    def auto_discard(self,seat):
        p=self.players[seat]
        if not p.hand:return
        t=self.ai_pick(p); p.hand.remove(t); p.discards.append(t); self.last_discard=t; self.last_discarder=seat; self.must_discard=False; self.add_log(f'{p.name} 打出 {TILE_NAMES[t]}。')
        self.advance(seat)
    def advance(self,seat):
        self.current=(seat+1)%4
        if self.players[self.current].human:self.draw(self.current); self.must_discard=True
        else:self.must_discard=False
        self.turn_at=time.time()
    def ai_until_human(self):
        with self.lock:
            self.timeout(); guard=0
            while self.phase=='playing' and guard<80 and not self.awaiting_claim and not self.players[self.current].human:
                guard+=1
                if not self.must_discard:self.draw(self.current); self.must_discard=True
                if self.phase!='playing':return
                if can_win_simple(self.players[self.current].hand,self.dragon):self.finish_win(self.current); return
                self.auto_discard(self.current)
    def discard(self,seat,pos):
        with self.lock:
            if self.phase!='playing' or self.current!=seat or not self.must_discard:return
            p=self.players[seat]
            if pos<0 or pos>=len(p.hand):return
            t=p.hand.pop(pos); p.discards.append(t); self.last_discard=t; self.last_discarder=seat; self.must_discard=False; self.add_log(f'{p.name} 打出 {TILE_NAMES[t]}。'); self.advance(seat)
        self.ai_until_human()
    def hu(self,seat):
        with self.lock:
            if self.phase=='playing' and self.current==seat and can_win_simple(self.players[seat].hand,self.dragon):self.finish_win(seat)
    def finish_win(self,w):
        for i,p in enumerate(self.players):
            if i!=w:p.score-=10; self.players[w].score+=10
        self.dealer=w if w==self.dealer else (self.dealer+1)%4; self.end_round(f'{self.players[w].name} 自摸胡，三家各付 10 分。')
    def state(self,seat):
        with self.lock:
            self.ai_until_human(); p=self.players[seat]; rem=max(0,TURN_SECONDS-int(time.time()-self.turn_at)) if self.phase=='playing' and self.players[self.current].human else TURN_SECONDS
            return {'room':self.room_id,'phase':self.phase,'ownerSeat':self.owner,'seat':seat,'name':p.name,'current':self.players[self.current].name,'wall':len(self.wall),'dragon':TILE_NAMES[self.dragon] if self.phase=='playing' else '未开局','dragonId':self.dragon,'remaining':rem,'canStart':self.phase=='lobby' and seat==self.owner and self.all_ready(),'canReady':self.phase=='lobby' and p.human,'ready':p.ready,'canAct':self.phase=='playing' and self.current==seat and self.must_discard,'hand':[{'id':t,'name':TILE_NAMES[t]} for t in p.hand],'players':[{'seat':i,'name':q.name,'human':q.human,'ready':q.ready,'owner':i==self.owner,'score':q.score,'handCount':len(q.hand),'discards':[{'id':t,'name':TILE_NAMES[t]} for t in q.discards[-28:]]} for i,q in enumerate(self.players)],'log':self.log[-18:]}

ROOMS={}; LOCK=threading.RLock()
def get_room(rid=None):
    with LOCK:
        rid=rid or ''.join(secrets.choice(string.ascii_uppercase+string.digits) for _ in range(6))
        if rid not in ROOMS:ROOMS[rid]=Room(rid)
        return ROOMS[rid]

HTML=r'''<!doctype html><html lang="zh-CN"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>小马识途麻将</title><style>body{margin:0;font-family:"Microsoft YaHei",Arial;background:radial-gradient(circle,#2b6b5d,#102823);color:#fff7e6}header{background:#0c1d1b;padding:12px 16px;font-size:22px;font-weight:800;color:#ffe8af;display:flex;justify-content:space-between}.tag{font-size:12px;color:#cdbb8a}.wrap{max-width:1180px;margin:auto;padding:8px}.panel{background:rgba(255,250,240,.96);color:#263238;border:1px solid #d9b56f;border-radius:10px;padding:10px;margin:10px;box-shadow:0 8px 24px #0005}.btn{padding:9px 13px;margin:4px;border:0;border-radius:7px;background:#263238;color:white;font-size:15px}.gold{background:#9b6a22}.red{background:#963232}.btn:disabled{opacity:.45}.table{position:relative;height:560px;border:8px solid #8c6334;border-radius:28px;background:radial-gradient(circle,#246555,#0c2926);box-shadow:inset 0 0 60px #0008}.center{position:absolute;left:50%;top:50%;transform:translate(-50%,-50%);width:210px;height:118px;border:2px solid #d9b56f;border-radius:18px;background:#071d1bcc;color:#ffe8af;display:flex;flex-direction:column;align-items:center;justify-content:center;font-weight:800}.timer{font-size:32px}.seat{position:absolute;min-width:165px;background:#071d1bcc;border:1px solid #d9b56f;border-radius:12px;padding:8px;color:#ffe8af}.seat span{display:block;font-size:12px;color:#ded2af}.bottom{left:50%;bottom:8px;transform:translateX(-50%)}.top{left:50%;top:8px;transform:translateX(-50%)}.right{right:8px;top:50%;transform:translateY(-50%)}.left{left:8px;top:50%;transform:translateY(-50%)}.pile{position:absolute;display:grid;gap:4px}.pb{left:50%;bottom:98px;transform:translateX(-50%);grid-template-columns:repeat(10,34px)}.pt{left:50%;top:98px;transform:translateX(-50%);grid-template-columns:repeat(10,34px);direction:rtl}.pr{right:180px;top:50%;transform:translateY(-50%);grid-template-columns:repeat(3,48px)}.pl{left:180px;top:50%;transform:translateY(-50%);grid-template-columns:repeat(3,48px)}.tile{width:46px;height:64px;border:2px solid #6e6256;border-radius:7px;background:linear-gradient(#fffef9,#eadfc9);box-shadow:2px 3px 0 #9e8d78;font-weight:800;font-size:16px;color:#263238}.river{width:34px;height:48px;font-size:13px}.side{width:48px;height:34px;font-size:13px}.dragon{background:linear-gradient(#ffe8a8,#f3c664)}.hand{display:flex;gap:6px;flex-wrap:wrap;justify-content:center}.lobby{display:flex;gap:10px;flex-wrap:wrap}.card{min-width:170px;background:#fffaf0;border:1px solid #dac190;border-radius:8px;padding:8px}.log{max-height:130px;overflow:auto;font-size:13px;color:#5f5448}.hide{display:none}input{font-size:16px;padding:8px;width:160px}</style><header><div>小马识途麻将</div><div class="tag">孙哥开发 · 云端房间</div></header><main class="wrap"><div id="join" class="panel"><b>加入云端房间</b><input id="name" placeholder="你的名字"><button class="btn gold" onclick="join()">入座</button><div>把当前网址发给朋友即可加入同一房间。</div></div><div id="game" class="hide"><div class="panel"><b id="seat"></b><div id="info"></div><button id="readyBtn" class="btn gold" onclick="ready()">准备</button><button id="startBtn" class="btn gold" onclick="startGame()">房主开始</button><button class="btn red" onclick="leaveSeat()">退出托管</button><button class="btn" onclick="hu()">自摸胡</button></div><div id="lobby" class="panel"><b>等待准备</b><div id="lobbyPlayers" class="lobby"></div><div>所有真人准备后，房主点击开始。每局结束后都要重新准备。</div></div><div class="table"><div class="center"><div>小马识途</div><div id="timer" class="timer">30</div><div id="roundState">等待中</div></div><div id="n0" class="seat bottom"></div><div id="n1" class="seat right"></div><div id="n2" class="seat top"></div><div id="n3" class="seat left"></div><div id="p0" class="pile pb"></div><div id="p1" class="pile pr"></div><div id="p2" class="pile pt"></div><div id="p3" class="pile pl"></div></div><div class="panel"><b>我的手牌</b><div id="hand" class="hand"></div><div>轮到你时点牌打出。30 秒不出牌会自动托管。</div></div><div class="panel"><b>流水</b><div id="log" class="log"></div></div></div><script>const room=location.pathname.split('/').filter(Boolean).pop()||'';let key='xmst_'+room,saved=JSON.parse(localStorage.getItem(key)||'{}'),seat=saved.seat??-1,token=saved.token||'';async function post(a,d){return fetch(a,{method:'POST',headers:{'Content-Type':'application/x-www-form-urlencoded'},body:new URLSearchParams(d)}).then(r=>r.json())}async function join(){let r=await post('/api/join/'+room,{name:document.getElementById('name').value||'好友',token});if(r.ok){seat=r.seat;token=r.token;localStorage.setItem(key,JSON.stringify({seat,token}));tick()}else alert(r.error)}async function act(a,d={}){let r=await post('/api/'+a+'/'+room,{seat,token,...d});if(!r.ok&&r.error)alert(r.error);setTimeout(tick,120)}async function discard(i){await act('discard',{pos:i})}async function ready(){await act('ready')}async function startGame(){await act('start')}async function leaveSeat(){await act('leave');localStorage.removeItem(key);seat=-1;token='';tick()}async function hu(){await act('hu')}function rel(a,m){return(a-m+4)%4}let S=null;function th(x,side){return`<button class="tile ${side?'side':'river'} ${x.id==S.dragonId?'dragon':''}">${x.name}</button>`}function render(s){S=s;for(let i=0;i<4;i++){document.getElementById('p'+i).innerHTML='';document.getElementById('n'+i).innerHTML=''}s.players.forEach(p=>{let r=rel(p.seat,s.seat),flag=(p.owner?' 房主':'')+(p.human?(p.ready?' 已准备':' 未准备'):' 电脑');document.getElementById('n'+r).innerHTML=`<b>${p.name}${p.seat==s.seat?'（我）':''}</b><span>${flag} · 手牌 ${p.handCount} · ${p.score}分</span>`;document.getElementById('p'+r).innerHTML=p.discards.map(x=>th(x,r==1||r==3)).join('')});document.getElementById('lobby').classList.toggle('hide',s.phase!='lobby');document.getElementById('lobbyPlayers').innerHTML=s.players.map(p=>`<div class="card"><b>${p.name}${p.seat==s.seat?'（我）':''}</b><br>${p.human?(p.ready?'已准备':'未准备'):'电脑补位'}${p.owner?' · 房主':''}</div>`).join('')}async function tick(){if(seat<0||!token){document.getElementById('join').style.display='block';document.getElementById('game').classList.add('hide');return}let s=await fetch('/api/state/'+room+'?seat='+seat+'&token='+encodeURIComponent(token)).then(r=>r.json());if(!s.ok){document.getElementById('join').style.display='block';document.getElementById('game').classList.add('hide');return}document.getElementById('join').style.display='none';document.getElementById('game').classList.remove('hide');document.getElementById('seat').textContent=s.name+'（房间 '+s.room+'）';document.getElementById('info').textContent=`阶段：${s.phase=='lobby'?'准备中':'游戏中'} 当前：${s.current} 剩余牌：${s.wall} 龙牌：${s.dragon} ${s.canAct?'轮到你出牌':'等待中'}`;document.getElementById('timer').textContent=s.remaining;document.getElementById('roundState').textContent=s.phase=='lobby'?'准备中':'出牌中';document.getElementById('readyBtn').disabled=!s.canReady;document.getElementById('readyBtn').textContent=s.ready?'取消准备':'准备';document.getElementById('startBtn').disabled=!s.canStart;document.getElementById('hand').innerHTML=s.hand.map((x,i)=>`<button class="tile ${x.id==s.dragonId?'dragon':''}" ${s.canAct?'':'disabled'} onclick="discard(${i})">${x.name}</button>`).join('');render(s);document.getElementById('log').innerHTML=s.log.join('<br>')}setInterval(tick,1000);tick()</script></main></html>'''
class H(BaseHTTPRequestHandler):
 def log_message(self,*a): pass
 def text(self,t,ct='text/html; charset=utf-8'):
  b=t.encode('utf-8'); self.send_response(200); self.send_header('Content-Type',ct); self.send_header('Content-Length',str(len(b))); self.send_header('Cache-Control','no-store'); self.end_headers(); self.wfile.write(b)
 def js(self,o): self.text(json.dumps(o,ensure_ascii=False),'application/json; charset=utf-8')
 def do_GET(self):
  p=urlparse(self.path)
  if p.path=='/': r=get_room(); self.send_response(302); self.send_header('Location',f'/room/{r.room_id}/'); self.end_headers(); return
  if p.path.startswith('/room/'): get_room(p.path.strip('/').split('/')[-1].upper()); self.text(HTML); return
  if p.path.startswith('/api/state/'):
   rid=p.path.split('/')[-1].upper(); q=parse_qs(p.query); seat=int(q.get('seat',['-1'])[0]); token=q.get('token',[''])[0]; r=get_room(rid)
   if not r.auth(seat,token): self.js({'ok':False}); return
   s=r.state(seat); s['ok']=True; self.js(s); return
  self.send_response(404); self.end_headers()
 def do_POST(self):
  parts=urlparse(self.path).path.strip('/').split('/'); action,rid=parts[1],parts[2].upper(); r=get_room(rid); data=parse_qs(self.rfile.read(int(self.headers.get('Content-Length','0'))).decode())
  try:
   if action=='join': seat,token=r.join(data.get('name',['好友'])[0],data.get('token',[''])[0]); self.js({'ok':True,'seat':seat,'token':token}); return
   seat=int(data.get('seat',['-1'])[0]); token=data.get('token',[''])[0]
   if not r.auth(seat,token): self.js({'ok':False,'error':'auth'}); return
   if action=='ready': r.ready(seat)
   elif action=='start': r.start(seat)
   elif action=='leave': r.leave(seat)
   elif action=='discard': r.discard(seat,int(data.get('pos',['-1'])[0]))
   elif action=='hu': r.hu(seat)
   self.js({'ok':True})
  except Exception as e: self.js({'ok':False,'error':str(e)})
def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--host',default='0.0.0.0'); ap.add_argument('--port',type=int,default=int(os.environ.get('PORT','8000'))); a=ap.parse_args(); ThreadingHTTPServer((a.host,a.port),H).serve_forever()
if __name__=='__main__': main()

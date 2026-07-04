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

def can_make_sets_key(key,wilds,memo=None):
    memo=memo or {}
    state=(key,wilds)
    if state in memo:return memo[state]
    c=list(key); i=next((x for x,v in enumerate(c) if v),-1)
    if i<0:
        memo[state]=(wilds%3==0); return memo[state]
    if c[i]>=3:
        c[i]-=3
        if can_make_sets_key(tuple(c),wilds,memo): memo[state]=True; return True
        c[i]+=3
    need_triplet=3-c[i]
    if 0<need_triplet<=wilds:
        old=c[i]; c[i]=0
        if can_make_sets_key(tuple(c),wilds-need_triplet,memo): memo[state]=True; return True
        c[i]=old
    if i<27 and i%9<=6:
        need=0; used=[]
        for j in (i,i+1,i+2):
            if c[j]>0: used.append(j)
            else: need+=1
        if need<=wilds:
            for j in used:c[j]-=1
            if can_make_sets_key(tuple(c),wilds-need,memo): memo[state]=True; return True
            for j in used:c[j]+=1
    memo[state]=False; return False

def can_win_simple(hand,wild):
    if len(hand)%3!=2 or len(hand)<14:return False
    wilds=sum(1 for t in hand if t==wild)
    c=counts(t for t in hand if t!=wild)
    if wilds>=2 and can_make_sets_key(tuple(c),wilds-2):return True
    for i in range(34):
        if c[i]>=2:
            c[i]-=2
            if can_make_sets_key(tuple(c),wilds): c[i]+=2; return True
            c[i]+=2
        if c[i]>=1 and wilds>=1:
            c[i]-=1
            if can_make_sets_key(tuple(c),wilds-1): c[i]+=1; return True
            c[i]+=1
    return False

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
                    if self.phase=='playing':
                        self.end_round(f'{p.name} 中途加入，本局结束，请重新准备开始新对局。')
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
            self.add_log(f'{old} 退出游戏，当前位置由电脑补位。')
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
        self.add_log(f'{self.players[self.current].name} 超时，系统自动出牌。'); self.auto_discard(self.current)
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
            if self.phase=='playing' and self.current==seat and can_win_simple(self.players[seat].hand,self.dragon):
                self.finish_win(seat)
            else:
                self.add_log(f'{self.players[seat].name} 现在不能胡。')
    def finish_win(self,w):
        for i,p in enumerate(self.players):
            if i!=w:p.score-=10; self.players[w].score+=10
        self.dealer=w if w==self.dealer else (self.dealer+1)%4; self.end_round(f'{self.players[w].name} 自摸胡，三家各付 10 分。')
    def state(self,seat):
        with self.lock:
            self.ai_until_human(); p=self.players[seat]; rem=max(0,TURN_SECONDS-int(time.time()-self.turn_at)) if self.phase=='playing' and self.players[self.current].human else TURN_SECONDS
            can_hu=self.phase=='playing' and self.current==seat and self.must_discard and can_win_simple(p.hand,self.dragon)
            return {'room':self.room_id,'phase':self.phase,'ownerSeat':self.owner,'seat':seat,'name':p.name,'current':self.players[self.current].name,'currentSeat':self.current,'wall':len(self.wall),'dragon':TILE_NAMES[self.dragon] if self.phase=='playing' else '未开局','dragonId':self.dragon,'remaining':rem,'canStart':self.phase=='lobby' and seat==self.owner and self.all_ready(),'canReady':self.phase=='lobby' and p.human,'ready':p.ready,'canAct':self.phase=='playing' and self.current==seat and self.must_discard,'canHu':can_hu,'lastDiscard':({'id':self.last_discard,'name':TILE_NAMES[self.last_discard]} if self.last_discard is not None else None),'lastDiscarder':self.last_discarder,'lastDiscarderName':(self.players[self.last_discarder].name if self.last_discarder is not None else ''),'hand':[{'id':t,'name':TILE_NAMES[t]} for t in p.hand],'players':[{'seat':i,'name':q.name,'human':q.human,'ready':q.ready,'owner':i==self.owner,'score':q.score,'handCount':len(q.hand),'discards':[{'id':t,'name':TILE_NAMES[t]} for t in q.discards[-28:]]} for i,q in enumerate(self.players)],'log':self.log[-18:]}

ROOMS={}; LOCK=threading.RLock()
def get_room(rid=None):
    with LOCK:
        rid=rid or ''.join(secrets.choice(string.ascii_uppercase+string.digits) for _ in range(6))
        if rid not in ROOMS:ROOMS[rid]=Room(rid)
        return ROOMS[rid]

HTML=r'''<!doctype html><html lang="zh-CN"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1"><title>小马识途麻将</title><style>
*{box-sizing:border-box}body{margin:0;min-height:100vh;overflow:hidden;font-family:"Microsoft YaHei",Arial,sans-serif;background:#061817;color:#f7edd1}.hide{display:none!important}button{font:inherit}.game{position:fixed;inset:0;background:radial-gradient(circle at 50% 42%,#2d6f71 0,#113b3c 42%,#061818 100%);overflow:hidden}.game:before{content:"";position:absolute;inset:10% 18%;border-radius:50%;border:2px solid rgba(201,229,217,.08);box-shadow:0 0 80px rgba(126,206,185,.12) inset}.topbar{position:absolute;left:18px;top:14px;z-index:10;display:flex;gap:10px;align-items:center}.brand{padding:8px 12px;border-radius:12px;background:linear-gradient(#d8442f,#9c241a);border:2px solid #f5c96c;color:#fff2bd;font-weight:900;box-shadow:0 4px 14px #0008}.round{font-size:13px;color:#ffe7a0;text-shadow:0 2px 3px #000}.join,.lobbyBox{position:absolute;left:50%;top:50%;transform:translate(-50%,-50%);z-index:20;width:min(460px,90vw);background:rgba(8,25,25,.92);border:1px solid #b99b62;border-radius:14px;padding:18px;box-shadow:0 16px 46px #000b}.join h2,.lobbyBox h2{margin:0 0 14px;color:#ffe7a0}.join input{width:100%;padding:12px;border:1px solid #c8ad78;border-radius:9px;background:#fffdf0;font-size:18px}.btn{border:0;border-radius:9px;padding:10px 16px;margin:8px 5px 0 0;background:#28484a;color:#fff;cursor:pointer}.gold{background:linear-gradient(#d7a94c,#93621d)}.red{background:linear-gradient(#b8493e,#84221d)}.btn:disabled{opacity:.42;cursor:not-allowed}.seat{position:absolute;z-index:3;width:150px;text-align:center;color:#f9e8a9}.avatar{width:72px;height:72px;margin:auto;border-radius:12px;background:linear-gradient(135deg,#f7c16a,#8e372f);border:3px solid #34302b;display:grid;place-items:center;font-size:34px;box-shadow:0 8px 18px #0008}.active .avatar{border-color:#ffd25a;box-shadow:0 0 22px #ffd25a}.seatName{margin:3px auto 0;padding:3px 8px;width:max-content;max-width:150px;border-radius:5px;background:#071515cc;color:#ffe484;font-weight:800}.seatMeta{font-size:12px;color:#d7d6c6}.me{left:42px;bottom:110px}.right{right:40px;top:38%;transform:translateY(-50%)}.top{left:50%;top:16px;transform:translateX(-50%)}.left{left:42px;top:38%;transform:translateY(-50%)}.backs{position:absolute;display:flex;gap:3px;z-index:2}.backs.topBack{top:22px;left:50%;transform:translateX(-50%)}.backs.leftBack{left:210px;top:25%;flex-direction:column}.backs.rightBack{right:210px;top:25%;flex-direction:column}.back{width:38px;height:54px;border-radius:5px;background:linear-gradient(90deg,#eef4e7 0 18%,#45ad28 19% 100%);border:1px solid #165814;box-shadow:2px 2px 4px #0005}.leftBack .back,.rightBack .back{width:18px;height:42px}.center{position:absolute;left:50%;top:45%;transform:translate(-50%,-50%);z-index:4;width:150px;height:150px;border-radius:18px;background:linear-gradient(135deg,#111,#333);box-shadow:0 10px 24px #000b,inset 0 0 24px #000;border:2px solid #4a4a4a;display:grid;place-items:center}.wind{position:absolute;color:#ddd;font-size:28px;font-weight:900;text-shadow:0 2px 4px #000}.w0{bottom:9px;color:#8cff7e}.w1{right:15px}.w2{top:9px}.w3{left:15px}.timer{font-family:Consolas,monospace;font-size:58px;color:#cfe9ff;text-shadow:0 0 12px #64bcff}.turnGlow{position:absolute;inset:-8px;border-radius:24px;border:8px solid transparent}.turn0{border-bottom-color:#78ff66}.turn1{border-right-color:#78ff66}.turn2{border-top-color:#78ff66}.turn3{border-left-color:#78ff66}.wallCount{position:absolute;left:calc(50% + 95px);top:45%;transform:translateY(-50%);background:#46a92f;border:2px solid #246c20;border-radius:6px;padding:8px 10px;font-weight:900;box-shadow:0 5px 8px #0008}.dragonBox{position:absolute;left:calc(50% - 300px);top:45%;transform:translateY(-50%);display:flex;align-items:center;gap:10px;background:#123b42c9;border:1px solid #74a09c;border-radius:9px;padding:9px 12px;color:#fff}.lastShow{position:absolute;left:50%;top:31%;transform:translate(-50%,-50%);z-index:8;text-align:center;color:#ffe9aa;font-weight:900;min-height:98px}.lastShow .tile{animation:popIn .35s ease-out}.prompt{position:absolute;left:50%;bottom:178px;transform:translateX(-50%);z-index:8;background:#15263bcc;color:white;font-size:28px;padding:10px 34px;border-radius:4px;box-shadow:0 4px 14px #0007}.hand{position:absolute;left:50%;bottom:18px;transform:translateX(-50%);z-index:7;display:flex;gap:5px;max-width:82vw;justify-content:center}.tile{position:relative;width:58px;height:82px;border:2px solid #a9a083;border-radius:7px;background:linear-gradient(#fffff7,#eee8d2 54%,#d7cfb6);box-shadow:0 5px 0 #5f9637,3px 6px 10px #0008;color:#111;display:flex;align-items:center;justify-content:center;overflow:hidden}.tile.big{width:74px;height:102px}.tile.river{width:46px;height:64px;box-shadow:0 4px 0 #63893d,2px 5px 9px #0008}.tile.side{width:46px;height:64px;box-shadow:0 4px 0 #63893d,2px 5px 9px #0008}.tile[disabled]{filter:grayscale(.2);opacity:.65}.tile.dragonTile{background:linear-gradient(#fff7c8,#ebcb69)}.face{position:relative;z-index:1;display:grid;place-items:center}.mahjongGlyph{position:relative;z-index:1;font-size:48px;line-height:1;font-family:"Segoe UI Symbol","Noto Sans Symbols2",serif}.river .mahjongGlyph{font-size:30px}.side .mahjongGlyph{font-size:24px}.char{font-family:KaiTi,"STKaiti",serif;font-size:42px;font-weight:900;line-height:.8}.river .char{font-size:24px}.side .char{font-size:20px}.wan .char{color:#b51618}.honor .char{color:#111}.honor.red .char,.dragonText{color:#bd1515}.bamboo,.dotGrid{display:grid;gap:3px}.dotGrid{grid-template-columns:repeat(3,12px);grid-auto-rows:12px}.river .dotGrid{grid-template-columns:repeat(3,6px);grid-auto-rows:6px}.dot{border:2px solid #136d43;border-radius:50%;background:radial-gradient(circle,#d9282d 0 25%,#fff 27% 45%,#17935a 47% 100%)}.bamboo{grid-template-columns:repeat(3,7px);grid-auto-rows:18px}.river .bamboo{grid-template-columns:repeat(3,3px);grid-auto-rows:9px}.bam{border-radius:8px;background:linear-gradient(90deg,#0c7d42,#58bf74,#0c7d42)}.riverArea{position:absolute;z-index:5;display:grid;gap:6px}.river0{left:38%;bottom:34%;transform:translateX(-50%);grid-template-columns:repeat(6,46px)}.river2{left:50%;top:10%;transform:translateX(-50%);grid-template-columns:repeat(6,46px)}.river1{right:33%;top:24%;transform:none;grid-template-columns:repeat(4,46px)}.river3{left:27%;top:28%;transform:none;grid-template-columns:repeat(4,46px)}.sideMenu{position:absolute;right:18px;top:22px;z-index:12;width:110px;text-align:center}.huFloat{position:absolute;left:50%;bottom:128px;transform:translateX(-50%);z-index:16;width:78px;height:78px;border-radius:50%;display:grid;place-items:center;background:radial-gradient(circle,#fff6a6 0,#d99423 58%,#8f4811 100%);border:3px solid #ffe9a0;color:white;font-size:38px;font-family:KaiTi,"STKaiti",serif;font-weight:900;text-shadow:0 3px 4px #7a2500;box-shadow:0 0 22px #ffd35e;cursor:pointer}.roundBtn{width:78px;height:78px;margin:8px auto;border-radius:50%;border:3px solid #ffe9a0;background:radial-gradient(circle,#fff6a6 0,#d99423 58%,#8f4811 100%);color:white;font-weight:900;font-size:38px;font-family:KaiTi,"STKaiti",serif;text-shadow:0 3px 4px #7a2500;box-shadow:0 0 22px #ffd35e}.exitItem{display:flex;align-items:center;gap:8px;justify-content:center;margin-top:12px;font-size:24px;font-weight:900;color:#ffeec0;cursor:pointer}.exitItem:before{content:"←";font-size:44px}.logPanel{position:absolute;left:14px;bottom:12px;z-index:15;width:260px;max-height:150px;overflow:auto;background:#fff8e8e8;color:#2b2b24;border-radius:8px;padding:8px;font-size:12px}.lobbyCards{display:grid;grid-template-columns:repeat(2,1fr);gap:8px}.card{border:1px solid #8f7750;border-radius:8px;padding:9px;background:#fff8e8;color:#222}@keyframes popIn{0%{transform:translateY(-34px) scale(.65);opacity:0}65%{transform:translateY(4px) scale(1.12)}100%{transform:translateY(0) scale(1);opacity:1}}@media(max-width:820px){.game{overflow:auto}.tile{width:43px;height:62px}.hand{max-width:96vw}.seat{width:110px}.avatar{width:52px;height:52px}.backs.leftBack,.backs.rightBack{display:none}.river1{right:120px}.river3{left:120px}.sideMenu{right:6px}.logPanel{display:none}.prompt{font-size:18px;bottom:145px}.center{width:112px;height:112px}.timer{font-size:42px}}
.tileFace{position:relative;z-index:1;width:100%;height:100%;display:grid;place-items:center;padding:8px 6px 10px}.wanFace{font-family:KaiTi,"STKaiti",serif;font-weight:900;color:#b51616;text-align:center;line-height:.78}.wanFace .top{position:static;transform:none;font-size:32px;display:block}.wanFace .bottom{font-size:22px;display:block;margin-top:4px}.honorFace{font-family:KaiTi,"STKaiti",serif;font-size:40px;font-weight:900;line-height:1;color:#111}.honorFace.red{color:#b51616}.tongGrid{display:grid;grid-template-columns:repeat(3,13px);grid-auto-rows:13px;gap:3px}.tongDot{border:2px solid #243a68;border-radius:50%;background:radial-gradient(circle,#c92a2a 0 23%,#fff 25% 43%,#2d4172 45% 100%)}.tiaoGrid{display:grid;grid-template-columns:repeat(3,8px);grid-auto-rows:17px;gap:3px}.tiaoStick{border-radius:8px;background:linear-gradient(90deg,#0d642e,#4fab5a 45%,#0d642e);border:1px solid #095024}.bird{font-size:36px;color:#0f6a35;text-shadow:0 1px #fff}.river .tileFace{padding:4px 3px 5px}.river .wanFace .top{font-size:18px}.river .wanFace .bottom{font-size:13px;margin-top:2px}.river .honorFace{font-size:24px}.river .tongGrid{grid-template-columns:repeat(3,7px);grid-auto-rows:7px;gap:1px}.river .tongDot{border-width:1px}.river .tiaoGrid{grid-template-columns:repeat(3,4px);grid-auto-rows:8px;gap:1px}.river .bird{font-size:20px}.side .tileFace{padding:4px 3px 5px}.side .wanFace .top{font-size:18px}.side .wanFace .bottom{font-size:13px;margin-top:2px}.side .honorFace{font-size:24px}.side .tongGrid{grid-template-columns:repeat(3,7px);grid-auto-rows:7px;gap:1px}.side .tongDot{border-width:1px}.side .tiaoGrid{grid-template-columns:repeat(3,4px);grid-auto-rows:8px;gap:1px}.side .bird{font-size:20px}.tileSvg{position:relative;z-index:2;width:100%;height:100%;display:block}.tile:before{background:#fffdf7}.river .tileSvg,.side .tileSvg{width:100%;height:100%}</style><div class="game"><div id="join" class="join"><h2>小马识途麻将</h2><input id="name" placeholder="你的名字"><button class="btn gold" onclick="join()">入座</button><p>把当前网址发给朋友，朋友点击即可进入同一房间。</p></div><div id="game" class="hide"><div class="topbar"><div class="brand">余姚瞎子麻将</div><div class="round" id="topInfo">等待开局</div></div><div id="lobby" class="lobbyBox"><h2>等待准备</h2><div id="lobbyPlayers" class="lobbyCards"></div><button id="readyBtn" class="btn gold" onclick="ready()">准备</button><button id="startBtn" class="btn gold" onclick="startGame()">房主开始</button><button class="btn red" onclick="leaveSeat()">退出游戏</button></div><div id="s0" class="seat me"></div><div id="s1" class="seat right"></div><div id="s2" class="seat top"></div><div id="s3" class="seat left"></div><div id="b1" class="backs rightBack"></div><div id="b2" class="backs topBack"></div><div id="b3" class="backs leftBack"></div><div class="center"><div id="turnGlow" class="turnGlow turn0"></div><div class="wind w0">东</div><div class="wind w1">南</div><div class="wind w2">西</div><div class="wind w3">北</div><div id="timer" class="timer">30</div></div><div id="wall" class="wallCount">0</div><div class="dragonBox"><div id="dragonTile"></div><span id="dragonName">龙牌</span></div><div id="lastShow" class="lastShow"></div><div id="prompt" class="prompt hide"></div><div id="huFloat" class="huFloat hide" onclick="hu()">胡</div><div id="p0" class="riverArea river0"></div><div id="p1" class="riverArea river1"></div><div id="p2" class="riverArea river2"></div><div id="p3" class="riverArea river3"></div><div id="hand" class="hand"></div><div class="sideMenu"><div class="exitItem" onclick="leaveSeat()">退出</div></div><div class="logPanel"><b>流水</b><div id="log"></div></div></div></div><script>
const room=location.pathname.split('/').filter(Boolean).pop()||'';let key='xmst_'+room,saved=JSON.parse(localStorage.getItem(key)||'{}'),seat=saved.seat??-1,token=saved.token||'',lastKey='';
async function post(a,d){return fetch(a,{method:'POST',headers:{'Content-Type':'application/x-www-form-urlencoded'},body:new URLSearchParams(d)}).then(r=>r.json())}
async function join(){let r=await post('/api/join/'+room,{name:document.getElementById('name').value||'好友',token});if(r.ok){seat=r.seat;token=r.token;localStorage.setItem(key,JSON.stringify({seat,token}));tick()}else alert(r.error)}
async function act(a,d={}){let r=await post('/api/'+a+'/'+room,{seat,token,...d});if(!r.ok&&r.error)alert(r.error);setTimeout(tick,120)}
async function discard(i){await act('discard',{pos:i})}async function ready(){await act('ready')}async function startGame(){await act('start')}async function leaveSeat(){await act('leave');localStorage.removeItem(key);seat=-1;token='';tick()}async function hu(){await act('hu')}
function rel(a,m){return(a-m+4)%4}function suit(id){return id<9?'wan':id<18?'tong':id<27?'tiao':'honor'}function num(id){return id%9+1}
const tileBase='https://cdn.jsdelivr.net/gh/samoheen/mahjong-tiles@master/hongkong/svg/';
function tileFile(id){if(id<9)return String(id+8).padStart(2,'0')+'-characters-'+(id+1)+'.svg';if(id<18)return String(id+8).padStart(2,'0')+'-circles-'+(id-8)+'.svg';if(id<27)return String(id+8).padStart(2,'0')+'-bamboos-'+(id-17)+'.svg';return ['04-east-wind.svg','05-south-wind.svg','06-west-wind.svg','07-north-wind.svg','03-red-dragon.svg','02-green-dragon.svg','01-white-dragon.svg'][id-27]}
function tileInner(x){return `<img src="${tileBase+tileFile(x.id)}" alt="${x.name}" style="position:relative;z-index:2;width:100%;height:100%;object-fit:contain;display:block;pointer-events:none">`}
function tile(x,cls='',dis=false){if(!x)return'';let id=x.id,k=suit(id);return `<button class="tile ${cls} ${k} ${id==S?.dragonId?'dragonTile':''}" ${dis?'disabled':''} title="${x.name}">${tileInner(x)}</button>`}let S=null;function renderSeats(s){for(let i=0;i<4;i++){document.getElementById('s'+i).innerHTML='';document.getElementById('p'+i).innerHTML=''}s.players.forEach(p=>{let r=rel(p.seat,s.seat),flag=(p.owner?'房主 ':'')+(p.human?(p.ready?'已准备':'未准备'):'电脑补位'),act=p.seat==s.currentSeat?' active':'';let el=document.getElementById('s'+r);el.className=el.className.replace(' active','')+act;el.innerHTML=`<div class="avatar">${p.human?'马':'机'}</div><div class="seatName">${p.name}${p.seat==s.seat?'（我）':''}</div><div class="seatMeta">${flag} · ${p.handCount}张 · ${p.score}分</div>`;document.getElementById('p'+r).innerHTML=p.discards.map(x=>tile(x,(r==1||r==3)?'side':'river')).join('')});for(let r=1;r<=3;r++){let p=s.players.find(x=>rel(x.seat,s.seat)==r),n=p?Math.max(0,p.handCount):0;document.getElementById('b'+r).innerHTML=Array.from({length:n},()=>'<i class="back"></i>').join('')}}
function render(s){S=s;renderSeats(s);document.getElementById('lobby').classList.toggle('hide',s.phase!='lobby');document.getElementById('lobbyPlayers').innerHTML=s.players.map(p=>`<div class="card"><b>${p.name}${p.seat==s.seat?'（我）':''}</b><br>${p.human?(p.ready?'已准备':'未准备'):'电脑补位'}${p.owner?' · 房主':''}<br>${p.score}分</div>`).join('');document.getElementById('readyBtn').disabled=!s.canReady;document.getElementById('readyBtn').textContent=s.ready?'取消准备':'准备';document.getElementById('startBtn').disabled=!s.canStart;document.getElementById('timer').textContent=s.remaining;document.getElementById('wall').textContent=s.wall;document.getElementById('topInfo').textContent=s.phase=='lobby'?'房间 '+s.room+' · 等待准备':`房间 ${s.room} · ${s.current} 出牌 · 龙牌 ${s.dragon}`;document.getElementById('turnGlow').className='turnGlow turn'+rel(s.currentSeat,s.seat);document.getElementById('dragonTile').innerHTML=s.phase=='playing'?tile({id:s.dragonId,name:s.dragon},'river'):'';document.getElementById('dragonName').textContent=s.phase=='playing'?'龙牌 '+s.dragon:'未开局';document.getElementById('hand').innerHTML=s.hand.map((x,i)=>`<button class="tile ${suit(x.id)} ${x.id==s.dragonId?'dragonTile':''}" ${s.canAct?'':'disabled'} onclick="discard(${i})">${tileInner(x)}</button>`).join('');let p=document.getElementById('prompt');p.classList.toggle('hide',s.phase!='playing');p.textContent=s.canAct?'轮到你出牌':`${s.current} 正在出牌`;let lk=s.lastDiscard?(s.lastDiscarder+'-'+s.lastDiscard.name+'-'+s.players[s.lastDiscarder]?.discards.length):'';if(s.lastDiscard&&lk!==lastKey){lastKey=lk;document.getElementById('lastShow').innerHTML='<div>'+s.lastDiscarderName+' 打出</div>'+tile(s.lastDiscard,'big')}document.getElementById('huFloat').classList.toggle('hide',!s.canHu);document.getElementById('log').innerHTML=s.log.join('<br>')}
async function tick(){if(seat<0||!token){document.getElementById('join').classList.remove('hide');document.getElementById('game').classList.add('hide');return}let s=await fetch('/api/state/'+room+'?seat='+seat+'&token='+encodeURIComponent(token)).then(r=>r.json()).catch(()=>({ok:false}));if(!s.ok){document.getElementById('join').classList.remove('hide');document.getElementById('game').classList.add('hide');return}document.getElementById('join').classList.add('hide');document.getElementById('game').classList.remove('hide');render(s)}setInterval(tick,1000);tick()
</script></html>'''
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










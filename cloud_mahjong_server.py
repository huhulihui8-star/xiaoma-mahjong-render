import argparse, json, math, os, random, secrets, string, threading, time
from dataclasses import dataclass, field
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

TILE_NAMES=[f"{n}{s}" for s in ("万","筒","条") for n in range(1,10)]+["东","南","西","北","中","发","白"]
DEFAULT_NAMES=["南家","下家","对家","上家"]
TURN_SECONDS=30
CLAIM_SECONDS=20
BASE_SCORE=1
SPECIAL_WINS={"十三不搭","对对碰","一杠一达","二杠二达","三杠","四龙","十一风","全风向"}

def counts(tiles):
    c=[0]*34
    for t in tiles:c[t]+=1
    return c

def next_dragon(indicator):
    if indicator<27:
        base=indicator//9*9; return base+(indicator-base+1)%9
    return [28,29,30,27,32,33,31][indicator-27]

def tile_obj(t): return {'id':t,'name':TILE_NAMES[t]}

def can_make_sets_count(c,wilds,sets_needed,memo=None):
    memo=memo or {}; state=(tuple(c),wilds,sets_needed)
    if state in memo:return memo[state]
    if sets_needed<0 or wilds<0:return False
    left=sum(c)
    if sets_needed==0:
        memo[state]=(left==0); return memo[state]
    if left+wilds!=sets_needed*3:
        memo[state]=False; return False
    i=next((x for x,v in enumerate(c) if v),-1)
    if i<0:
        memo[state]=(wilds>=sets_needed*3); return memo[state]
    if c[i]>=3:
        c[i]-=3
        if can_make_sets_count(c,wilds,sets_needed-1,memo): c[i]+=3; memo[state]=True; return True
        c[i]+=3
    need=3-c[i]
    if 0<need<=wilds:
        old=c[i]; c[i]=0
        if can_make_sets_count(c,wilds-need,sets_needed-1,memo): c[i]=old; memo[state]=True; return True
        c[i]=old
    if i<27 and i%9<=6:
        used=[]; need=0
        for j in (i,i+1,i+2):
            if c[j]>0: used.append(j)
            else: need+=1
        if need<=wilds:
            for j in used:c[j]-=1
            if can_make_sets_count(c,wilds-need,sets_needed-1,memo):
                for j in used:c[j]+=1
                memo[state]=True; return True
            for j in used:c[j]+=1
    memo[state]=False; return False

def standard_win(hand,wild,meld_count=0):
    sets_needed=4-meld_count
    if sets_needed<0 or len(hand)!=sets_needed*3+2:return False
    wilds=sum(1 for t in hand if t==wild); c=counts(t for t in hand if t!=wild)
    if wilds>=2 and can_make_sets_count(c[:],wilds-2,sets_needed):return True
    for i in range(34):
        if c[i]>=2:
            c[i]-=2
            if can_make_sets_count(c[:],wilds,sets_needed): c[i]+=2; return True
            c[i]+=2
        if c[i]>=1 and wilds>=1:
            c[i]-=1
            if can_make_sets_count(c[:],wilds-1,sets_needed): c[i]+=1; return True
            c[i]+=1
    return False

def thirteen_unconnected(hand,wild):
    if len(hand)!=14:return False
    plain=[t for t in hand if t!=wild]; c=counts(plain)
    if any(v>1 for v in c):return False
    for suit in range(3):
        nums=[t%9 for t in plain if t//9==suit]
        for i,a in enumerate(nums):
            for b in nums[i+1:]:
                if abs(a-b)<3:return False
    return True

def all_triplets(hand,wild,melds):
    if any(m.get('type')=='chi' for m in melds):return False
    sets_needed=4-len(melds)
    if len(hand)!=sets_needed*3+2:return False
    wilds=sum(1 for t in hand if t==wild); c=counts(t for t in hand if t!=wild)
    pair_options=[None]+[i for i,v in enumerate(c) if v>0]
    for pair in pair_options:
        cc=c[:]; ww=wilds
        if pair is None:
            if ww<2:continue
            ww-=2
        elif cc[pair]>=2: cc[pair]-=2
        elif cc[pair]>=1 and ww>=1: cc[pair]-=1; ww-=1
        else: continue
        ok=True
        for i,v in enumerate(cc):
            if v:
                need=(3-v%3)%3
                if need>ww: ok=False; break
                ww-=need; cc[i]=0
        if ok and ww%3==0:return True
    return False

def win_types(hand,wild,melds=None,dragon_blocked=False):
    melds=melds or []
    if dragon_blocked:return []
    kong_count=sum(1 for m in melds if m.get('type')=='gang')
    dragon_count=sum(1 for t in hand if t==wild)
    honors=sum(1 for t in hand if t>=27)
    types=[]
    if standard_win(hand,wild,len(melds)):types.append('4面子1对子')
    if thirteen_unconnected(hand,wild):types.append('十三不搭')
    if all_triplets(hand,wild,melds):types.append('对对碰')
    if kong_count>=1 and dragon_count>=1:types.append('一杠一达')
    if kong_count>=2 and dragon_count>=2:types.append('二杠二达')
    if kong_count>=3:types.append('三杠')
    if dragon_count>=4:types.append('四龙')
    if honors>=11:types.append('十一风')
    if hand and all(t>=27 or t==wild for t in hand):types.append('全风向')
    return types

def best_win_rank(types): return 2 if any(t in SPECIAL_WINS for t in types) else (1 if types else 0)

def suit_bucket(t):
    if t<9:return "wan"
    if t<18:return "tong"
    if t<27:return "tiao"
    return "honor"

def tile_without_one(tiles,tile):
    x=list(tiles)
    if tile in x:x.remove(tile)
    return x

def has_one_number_suit(tiles,wild):
    suits={suit_bucket(t) for t in tiles if t!=wild and t<27}
    return len(suits)==1 and bool(suits)

def is_seven_pairs(tiles,wild):
    if len(tiles)!=14:return False
    c=counts(t for t in tiles if t!=wild); wilds=sum(1 for t in tiles if t==wild); singles=sum(1 for v in c if v%2)
    return singles<=wilds and (wilds-singles)%2==0

def is_seven_honors(tiles,wild):
    honors={t for t in tiles if t>=27 and t!=wild}
    return len(honors)>=7

def all_honors_or_dragons(tiles,wild):
    return bool(tiles) and all(t>=27 or t==wild for t in tiles)

def winning_wait_count(before,wild,melds):
    wins=[]
    for t in range(34):
        if win_types(before+[t],wild,melds,dragon_blocked=False):wins.append(t)
    return wins

@dataclass
class WinContext:
    winner:int
    win_method:str
    winning_tile:int|None
    discarder:int|None
    before_win_hand:list
    after_win_hand:list
    melds:list
    win_types:list
    wild:int
    is_dealer:bool=False
    dealer_streak:int=0
    wall_remaining:int=0
    turn_index:int=0
    first_discard_done:bool=False

def score_dragon_patterns(ctx):
    hand=list(ctx.after_win_hand); before=list(ctx.before_win_hand); melds=list(ctx.melds)
    wild=ctx.wild; c=counts(hand); dragon_count=c[wild]
    kong_count=sum(1 for m in melds if m.get('type')=='gang')
    patterns=[]
    def add(name,dragons,full=False):patterns.append({'name':name,'dragons':dragons,'full':full})
    if "4面子1对子" in ctx.win_types:add("平胡",1)
    if all_triplets(hand,wild,melds):add("大对对",1); add("对对碰",1)
    if has_one_number_suit(hand,wild):add("混一色",1)
    if thirteen_unconnected(hand,wild):add("十三不搭",1)
    if is_seven_honors(hand,wild):add("七风齐",1)
    if kong_count>=1 and dragon_count>=1:add("一杠一达",1)
    if kong_count>=2 and dragon_count>=2:add("二杠二达",1)
    if dragon_count==0:add("无龙",2)
    if dragon_count==1:add("一龙",1)
    if dragon_count==2:add("二龙",2)
    if dragon_count==3:add("三龙",3)
    if dragon_count>=4:add("四龙",100,ctx.win_method=="discard_win")
    if has_one_number_suit(hand,wild) and dragon_count>0:add("有龙清一色",10)
    if has_one_number_suit(hand,wild) and dragon_count==0:add("无龙清一色",100,ctx.win_method=="discard_win")
    waits=winning_wait_count(before,wild,melds) if before else []
    if len(waits)==1:
        add("单吊，胡相同牌" if ctx.winning_tile==wild else "单吊，胡不同牌",10,ctx.win_method=="discard_win")
    if ctx.is_dealer and not ctx.first_discard_done:add("天胡",10)
    if (not ctx.is_dealer) and ctx.turn_index<=1 and ctx.win_method in ("self_draw","gang_draw"):add("地胡",10)
    if ctx.win_method=="gang_draw":add("杠爆",10)
    if ctx.win_method=="robbed_kong":add("拉杠胡",10)
    if ctx.win_method in ("self_draw","gang_draw") and before:
        can_win_any=all(win_types(before+[t],wild,melds,dragon_blocked=False) for t in range(34))
        if can_win_any:add("龙抛龙" if ctx.winning_tile==wild else "抛龙",10)
    if ctx.wall_remaining==0 and ctx.win_method in ("self_draw","gang_draw"):add("海底捞月",10)
    if is_seven_pairs(hand,wild) and dragon_count==0:add("清七对",100,ctx.win_method=="discard_win")
    if kong_count>=3:add("三杠",100,ctx.win_method=="discard_win")
    if sum(1 for t in hand if t>=27)>=11:add("十一风",100,ctx.win_method=="discard_win")
    if all_honors_or_dragons(hand,wild):add("全风向",100,ctx.win_method=="discard_win")
    if not patterns:add("平胡",1)
    max_dragons=max(p['dragons'] for p in patterns)
    winners=[p for p in patterns if p['dragons']==max_dragons]
    return {'dragons':max_dragons,'patterns':[p['name'] for p in winners],'full_payout':any(p['full'] for p in winners)}

@dataclass
class Player:
    name:str
    human:bool=False
    token:str=""
    ready:bool=False
    hand:list=field(default_factory=list)
    discards:list=field(default_factory=list)
    melds:list=field(default_factory=list)
    score:int=0
    lastScoreText:str=""
    forbidden_discard:int|None=None
    pass_locks:list=field(default_factory=list)

class Room:
    def __init__(self,rid):
        self.room_id=rid; self.lock=threading.RLock(); self.players=[Player(DEFAULT_NAMES[i]) for i in range(4)]
        self.owner=None; self.phase='lobby'; self.wall=[]; self.dragon=0; self.dragon_indicator=None; self.current=0; self.dealer=0; self.dealer_streak=0; self.must_discard=False; self.turn_at=time.time(); self.log=[]; self.round_no=1
        self.last_discard=None; self.last_discarder=None; self.claim=None; self.circle_id=0
        self.last_draw_tile=None; self.pending_gang_draw=False; self.last_draw_was_gang=False; self.turn_index=0; self.first_discard_done=False; self.lastWinSummary=None; self.roundReveal=None
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
                    if self.phase=='playing': self.end_round(f'{p.name} 中途加入，本局结束，请重新准备开始新对局。')
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
            if self.claim and seat in self.claim.get('options',{}): self.pass_claim(seat,quiet=True)
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
            self.wall=list(range(34))*4; random.shuffle(self.wall)
            self.dragon_indicator=self.wall.pop(); self.dragon=next_dragon(self.dragon_indicator); self.current=self.dealer
            self.last_discard=None; self.last_discarder=None; self.claim=None; self.circle_id+=1; self.lastWinSummary=None; self.roundReveal=None
            self.last_draw_tile=None; self.pending_gang_draw=False; self.last_draw_was_gang=False; self.turn_index=0; self.first_discard_done=False
            for _ in range(13):
                for p in self.players:p.hand.append(self.wall.pop())
            self.players[self.dealer].hand.append(self.wall.pop())
            for p in self.players:p.hand.sort()
            self.phase='playing'; self.must_discard=True; self.turn_at=time.time(); self.add_log(f'第 {self.round_no} 局开始，庄家 {self.players[self.dealer].name}，翻牌 {TILE_NAMES[self.dragon_indicator]}，龙牌 {TILE_NAMES[self.dragon]}。'); self.round_no+=1
        self.ai_until_human()
    def end_round(self,msg):
        self.add_log(msg); self.phase='lobby'; self.must_discard=False; self.claim=None
        for p in self.players:
            if p.human:p.ready=False
            p.hand=[]; p.discards=[]; p.melds=[]; p.forbidden_discard=None; p.pass_locks=[]
        self.add_log('本局结束，请所有真人重新准备，房主再开始下一局。')
    def clean_locks_for(self,seat):
        p=self.players[seat]; p.pass_locks=[x for x in p.pass_locks if x.get('until')!=seat]
    def is_locked(self,seat,action,tile):
        return any(x.get('action')==action and x.get('tile')==tile for x in self.players[seat].pass_locks)
    def draw(self,seat):
        if not self.wall:self.dealer=(self.dealer+1)%4; self.dealer_streak=0; self.end_round('牌墙摸完，流局。'); return False
        self.clean_locks_for(seat); t=self.wall.pop(); self.players[seat].hand.append(t); self.players[seat].hand.sort(); self.current=seat; self.must_discard=True; self.turn_at=time.time(); self.last_draw_tile=t; self.last_draw_was_gang=self.pending_gang_draw; self.pending_gang_draw=False; self.turn_index+=1; return True
    def ai_pick(self,p):
        pool=[t for t in p.hand if t!=self.dragon and t!=p.forbidden_discard] or [t for t in p.hand if t!=self.dragon] or p.hand[:]
        c=counts(p.hand); pool.sort(key=lambda t:(c[t],random.random())); return pool[0]
    def timeout(self):
        if self.phase!='playing':return
        if self.claim and time.time()>=self.claim['deadline']:
            self.add_log('抢牌超时，自动过。'); self.finish_claim_window(); return
        if self.claim or not self.players[self.current].human or time.time()-self.turn_at<TURN_SECONDS:return
        self.add_log(f'{self.players[self.current].name} 超时，系统自动出牌。'); self.auto_discard(self.current)
    def auto_discard(self,seat):
        p=self.players[seat]
        if not p.hand:return
        t=self.ai_pick(p); self.discard_tile(seat,t)
    def discard_tile(self,seat,t):
        p=self.players[seat]
        if p.forbidden_discard==t:
            self.add_log(f'{p.name} 碰牌后本圈不能立刻打出 {TILE_NAMES[t]}。'); return False
        p.hand.remove(t); p.discards.append(t); p.forbidden_discard=None; self.last_discard=t; self.last_discarder=seat; self.must_discard=False; self.turn_at=time.time(); self.first_discard_done=True; self.add_log(f'{p.name} 打出 {TILE_NAMES[t]}。')
        self.open_claim_window(seat,t); return True
    def open_claim_window(self,discarder,tile):
        opts={}; self.circle_id+=1
        for off in range(1,4):
            s=(discarder+off)%4; p=self.players[s]; c=counts(p.hand); o={}
            hu=win_types(p.hand+[tile],self.dragon,p.melds,dragon_blocked=(tile==self.dragon or self.is_locked(s,'hu',tile)))
            if hu:o['hu']=hu
            if c[tile]>=2 and not self.is_locked(s,'peng',tile):o['peng']=True
            if c[tile]>=3 and not self.is_locked(s,'gang',tile):o['gang']=True
            if o:opts[s]=o
        if not opts:self.advance_after_claim(discarder); return
        self.claim={'tile':tile,'discarder':discarder,'circle':self.circle_id,'deadline':time.time()+CLAIM_SECONDS,'options':opts,'passed':set()}
        self.ai_resolve_claims()
    def ai_resolve_claims(self):
        if not self.claim:return
        humans=[s for s in self.claim['options'] if self.players[s].human]
        if humans:return
        order=[(self.claim['discarder']+i)%4 for i in range(1,4)]
        winners=[s for s in order if s in self.claim['options'] and self.claim['options'][s].get('hu')]
        if winners:
            winners.sort(key=lambda s:(-best_win_rank(self.claim['options'][s]['hu']),order.index(s)))
            self.claim_hu(winners[0]); return
        for s in order:
            o=self.claim['options'].get(s)
            if o and o.get('gang'): self.claim_gang(s); return
            if o and o.get('peng'): self.claim_peng(s); return
        self.finish_claim_window()
    def finish_claim_window(self):
        if not self.claim:return
        d=self.claim['discarder']; self.claim=None; self.advance_after_claim(d)
    def advance_after_claim(self,seat):
        self.claim=None; nxt=(seat+1)%4
        if self.draw(nxt): self.ai_until_human()
    def discard(self,seat,pos):
        with self.lock:
            if self.phase!='playing' or self.claim or self.current!=seat or not self.must_discard:return
            p=self.players[seat]
            if pos<0 or pos>=len(p.hand):return
            t=p.hand[pos]; ok=self.discard_tile(seat,t)
        if ok:self.ai_until_human()
    def remove_claimed_discard(self):
        if self.last_discarder is not None and self.players[self.last_discarder].discards and self.players[self.last_discarder].discards[-1]==self.last_discard:
            self.players[self.last_discarder].discards.pop()
    def pass_claim(self,seat,quiet=False):
        with self.lock:
            if not self.claim or seat not in self.claim['options']:return
            o=self.claim['options'][seat]; tile=self.claim['tile']; until=self.claim['discarder']
            for action in ('hu','peng','gang'):
                if action in o:self.players[seat].pass_locks.append({'action':action,'tile':tile,'until':until})
            self.claim['passed'].add(seat)
            if not quiet:self.add_log(f'{self.players[seat].name} 选择过。')
            if all(s in self.claim['passed'] for s in self.claim['options']): self.finish_claim_window()
        self.ai_until_human()
    def claim_hu(self,seat):
        with self.lock:
            if not self.claim or 'hu' not in self.claim['options'].get(seat,{}):return
            tile=self.claim['tile']; discarder=self.claim['discarder']; types=self.claim['options'][seat]['hu']; before=list(self.players[seat].hand); self.players[seat].hand.append(tile); self.players[seat].hand.sort(); self.remove_claimed_discard(); self.claim=None; self.finish_win(seat,discarder,types,before_hand=before,winning_tile=tile,win_method='discard_win')
    def claim_peng(self,seat):
        with self.lock:
            if not self.claim or not self.claim['options'].get(seat,{}).get('peng'):return
            tile=self.claim['tile']; p=self.players[seat]
            for _ in range(2):p.hand.remove(tile)
            p.melds.append({'type':'peng','tile':tile,'from':self.claim['discarder'],'concealed':False}); p.forbidden_discard=tile; self.remove_claimed_discard(); self.claim=None; self.current=seat; self.must_discard=True; self.turn_at=time.time(); self.add_log(f'{p.name} 碰 {TILE_NAMES[tile]}。')
        self.ai_until_human()
    def settle_gang_score(self,winner,payers,amount,label):
        total=0
        for i in payers:
            if i==winner:continue
            self.players[i].score-=amount; total+=amount; self.players[i].lastScoreText=f'-{amount} {label}'
        self.players[winner].score+=total; self.players[winner].lastScoreText=f'+{total} {label}'; self.add_log(f'{self.players[winner].name}{label}，获得 {total} 分。')
    def claim_gang(self,seat):
        with self.lock:
            if not self.claim or not self.claim['options'].get(seat,{}).get('gang'):return
            tile=self.claim['tile']; p=self.players[seat]
            for _ in range(3):p.hand.remove(tile)
            p.melds.append({'type':'gang','tile':tile,'from':self.claim['discarder'],'concealed':False}); self.remove_claimed_discard(); d=self.claim['discarder']; self.claim=None; self.settle_gang_score(seat,[d],BASE_SCORE*20,'直杠'); self.current=seat; self.must_discard=False; self.pending_gang_draw=True
            if self.draw(seat): self.add_log(f'{p.name} 杠后补牌。')
        self.ai_until_human()
    def gang(self,seat):
        with self.lock:
            if self.phase!='playing' or self.claim or self.current!=seat or not self.must_discard:return
            p=self.players[seat]; c=counts(p.hand)
            for tile,n in enumerate(c):
                if n>=4:
                    for _ in range(4):p.hand.remove(tile)
                    p.melds.append({'type':'gang','tile':tile,'from':seat,'concealed':True}); self.settle_gang_score(seat,[i for i in range(4) if i!=seat],BASE_SCORE*20,'暗杠'); self.must_discard=False; self.pending_gang_draw=True; self.draw(seat); break
            else:
                for m in p.melds:
                    if m.get('type')=='peng' and c[m['tile']]>=1:
                        tile=m['tile']; p.hand.remove(tile); m['type']='gang'; m['added']=True; self.settle_gang_score(seat,[i for i in range(4) if i!=seat],BASE_SCORE*10,'加杠'); self.must_discard=False; self.pending_gang_draw=True; self.draw(seat); break
        self.ai_until_human()
    def hu(self,seat):
        with self.lock:
            if self.claim:
                self.claim_hu(seat); return
            if self.phase=='playing' and self.current==seat and self.must_discard:
                types=win_types(self.players[seat].hand,self.dragon,self.players[seat].melds)
                if types:self.finish_win(seat,None,types,before_hand=tile_without_one(self.players[seat].hand,self.last_draw_tile),winning_tile=self.last_draw_tile,win_method=('gang_draw' if self.last_draw_was_gang else 'self_draw'))
                else:self.add_log(f'{self.players[seat].name} 现在不能胡。')
    def build_win_context(self,w,discarder,types,before_hand,winning_tile,win_method):
        return WinContext(winner=w,win_method=win_method,winning_tile=winning_tile,discarder=discarder,before_win_hand=list(before_hand or []),after_win_hand=list(self.players[w].hand),melds=[dict(m) for m in self.players[w].melds],win_types=list(types or []),wild=self.dragon,is_dealer=(w==self.dealer),dealer_streak=self.dealer_streak,wall_remaining=len(self.wall),turn_index=self.turn_index,first_discard_done=self.first_discard_done)
    def finish_win(self,w,discarder=None,types=None,before_hand=None,winning_tile=None,win_method=None):
        types=types or win_types(self.players[w].hand,self.dragon,self.players[w].melds)
        win_method=win_method or ('discard_win' if discarder is not None else ('gang_draw' if self.last_draw_was_gang else 'self_draw'))
        if before_hand is None:before_hand=tile_without_one(self.players[w].hand,winning_tile)
        ctx=self.build_win_context(w,discarder,types,before_hand,winning_tile,win_method)
        scoring=score_dragon_patterns(ctx); units=scoring['dragons']*BASE_SCORE; total=0; details=[]; score_before=[p.score for p in self.players]
        if discarder is None:
            for i in range(4):
                if i!=w:
                    self.players[i].score-=units; total+=units; self.players[i].lastScoreText=f'-{units} {scoring["dragons"]}龙'
            self.players[w].score+=total; self.players[w].lastScoreText=f'+{total} {scoring["dragons"]}龙'
            pay_text=f'自摸/平搓，三家各付 {units} 分'
        elif scoring['full_payout']:
            total=units*3; self.players[discarder].score-=total; self.players[discarder].lastScoreText=f'-{total} 冲击全缴'; self.players[w].score+=total; self.players[w].lastScoreText=f'+{total} 冲击全缴'
            pay_text=f'冲击全缴，{self.players[discarder].name} 独付 {total} 分'
        else:
            half=math.ceil(units*0.5)
            for i in range(4):
                if i==w:continue
                pay=units if i==discarder else half
                self.players[i].score-=pay; total+=pay; self.players[i].lastScoreText=f'-{pay} 点炮胡'; details.append(f'{self.players[i].name}-{pay}')
            self.players[w].score+=total; self.players[w].lastScoreText=f'+{total} 点炮胡'
            pay_text=f'点炮，{self.players[discarder].name}付 {units} 分，其他家各付 {half} 分'
        method_text={'self_draw':'自摸','discard_win':'点炮','gang_draw':'杠爆','robbed_kong':'拉杠胡'}.get(win_method,win_method)
        msg=f'{self.players[w].name} {method_text}胡 {scoring["dragons"]}龙（{"、".join(scoring["patterns"])}），{pay_text}。'
        self.lastWinSummary={'winner':self.players[w].name,'winnerSeat':w,'method':method_text,'dragons':scoring['dragons'],'patterns':scoring['patterns'],'baseTypes':ctx.win_types,'winningTile':(tile_obj(ctx.winning_tile) if ctx.winning_tile is not None else None),'fullPayout':scoring['full_payout'],'payText':pay_text,'scoreDelta':total}
        self.roundReveal=self.build_round_reveal(ctx,scoring,pay_text,method_text,score_before,total)
        if w==self.dealer:self.dealer_streak+=1
        else:self.dealer=(self.dealer+1)%4; self.dealer_streak=0
        self.end_round(msg)
    def ai_until_human(self):
        with self.lock:
            self.timeout(); guard=0
            while self.phase=='playing' and guard<120 and not self.claim and not self.players[self.current].human:
                guard+=1
                p=self.players[self.current]
                if not self.must_discard:
                    if not self.draw(self.current):return
                types=win_types(p.hand,self.dragon,p.melds)
                if types and random.random()<0.85:
                    self.finish_win(self.current,None,types); return
                self.auto_discard(self.current)
    def public_melds(self,p): return [{'type':m.get('type'),'tile':tile_obj(m.get('tile')),'concealed':m.get('concealed',False)} for m in p.melds]
    def build_round_reveal(self,ctx,scoring,pay_text,method_text,score_before,total):
        score_delta=[self.players[i].score-score_before[i] for i in range(4)]
        return {
            'room':self.room_id,
            'round':self.round_no-1,
            'winner':self.players[ctx.winner].name,
            'winnerSeat':ctx.winner,
            'discarderSeat':ctx.discarder,
            'discarderName':(self.players[ctx.discarder].name if ctx.discarder is not None else ''),
            'method':method_text,
            'dragons':scoring['dragons'],
            'dragon':tile_obj(self.dragon),
            'dragonIndicator':tile_obj(self.dragon_indicator) if self.dragon_indicator is not None else None,
            'winningTile':tile_obj(ctx.winning_tile) if ctx.winning_tile is not None else None,
            'baseTypes':list(ctx.win_types or []),
            'patterns':list(scoring['patterns']),
            'fullPayout':scoring['full_payout'],
            'payText':pay_text,
            'scoreDelta':total,
            'players':[{
                'seat':i,
                'name':p.name,
                'winner':i==ctx.winner,
                'discarder':i==ctx.discarder,
                'score':p.score,
                'delta':score_delta[i],
                'lastScoreText':p.lastScoreText,
                'hand':[tile_obj(t) for t in sorted(p.hand)],
                'melds':self.public_melds(p),
                'discards':[tile_obj(t) for t in p.discards],
            } for i,p in enumerate(self.players)]
        }
    def state(self,seat):
        with self.lock:
            self.timeout(); p=self.players[seat]
            claim_opts=self.claim['options'].get(seat,{}) if self.claim else {}
            can_hu=False; can_peng=False; can_gang=False; win_list=[]; claim_tile=None; claim_deadline=0
            if self.claim:
                can_hu='hu' in claim_opts; can_peng=bool(claim_opts.get('peng')); can_gang=bool(claim_opts.get('gang')); win_list=claim_opts.get('hu',[]); claim_tile=tile_obj(self.claim['tile']); claim_deadline=max(0,int(self.claim['deadline']-time.time()))
            elif self.phase=='playing' and self.current==seat and self.must_discard:
                win_list=win_types(p.hand,self.dragon,p.melds); can_hu=bool(win_list); c=counts(p.hand); can_gang=any(v>=4 for v in c) or any(m.get('type')=='peng' and c[m['tile']] for m in p.melds)
            rem=max(0,TURN_SECONDS-int(time.time()-self.turn_at)) if self.phase=='playing' and not self.claim and self.players[self.current].human else TURN_SECONDS
            return {'room':self.room_id,'phase':self.phase,'ownerSeat':self.owner,'seat':seat,'name':p.name,'current':self.players[self.current].name,'currentSeat':self.current,'wall':len(self.wall),'dragon':TILE_NAMES[self.dragon] if self.phase=='playing' else '未开局','dragonId':self.dragon,'dragonIndicator':(tile_obj(self.dragon_indicator) if self.dragon_indicator is not None else None),'remaining':rem,'claimDeadline':claim_deadline,'claimTile':claim_tile,'lastWinSummary':self.lastWinSummary,'roundReveal':self.roundReveal,'canStart':self.phase=='lobby' and seat==self.owner and self.all_ready(),'canReady':self.phase=='lobby' and p.human,'ready':p.ready,'canAct':self.phase=='playing' and not self.claim and self.current==seat and self.must_discard,'canHu':can_hu,'canPeng':can_peng,'canGang':can_gang,'winTypes':win_list,'lastDiscard':(tile_obj(self.last_discard) if self.last_discard is not None else None),'lastDiscarder':self.last_discarder,'lastDiscarderName':(self.players[self.last_discarder].name if self.last_discarder is not None else ''),'hand':[tile_obj(t) for t in p.hand],'melds':self.public_melds(p),'players':[{'seat':i,'name':q.name,'human':q.human,'ready':q.ready,'owner':i==self.owner,'score':q.score,'lastScoreText':q.lastScoreText,'handCount':len(q.hand),'kongCount':sum(1 for m in q.melds if m.get('type')=='gang'),'melds':self.public_melds(q),'discards':[tile_obj(t) for t in q.discards[-28:]]} for i,q in enumerate(self.players)],'log':self.log[-18:]}
ROOMS={}; LOCK=threading.RLock()
def get_room(rid=None):
    with LOCK:
        rid=rid or ''.join(secrets.choice(string.ascii_uppercase+string.digits) for _ in range(6))
        if rid not in ROOMS:ROOMS[rid]=Room(rid)
        return ROOMS[rid]

HTML=r'''<!doctype html><html lang="zh-CN"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1,viewport-fit=cover"><title>小马识途麻将</title><style>
*{box-sizing:border-box}body{margin:0;min-height:100vh;overflow:hidden;font-family:"Microsoft YaHei",Arial,sans-serif;background:#061817;color:#f7edd1}.hide{display:none!important}button{font:inherit}.game{position:fixed;inset:0;background:radial-gradient(circle at 50% 42%,#2d6f71 0,#113b3c 42%,#061818 100%);overflow:hidden}.game:before{content:"";position:absolute;inset:10% 18%;border-radius:50%;border:2px solid rgba(201,229,217,.08);box-shadow:0 0 80px rgba(126,206,185,.12) inset}.topbar{position:absolute;left:18px;top:14px;z-index:10;display:flex;gap:10px;align-items:center}.brand{padding:8px 12px;border-radius:12px;background:linear-gradient(#d8442f,#9c241a);border:2px solid #f5c96c;color:#fff2bd;font-weight:900;box-shadow:0 4px 14px #0008}.round{font-size:13px;color:#ffe7a0;text-shadow:0 2px 3px #000}.join,.lobbyBox{position:absolute;left:50%;top:50%;transform:translate(-50%,-50%);z-index:20;width:min(460px,90vw);background:rgba(8,25,25,.92);border:1px solid #b99b62;border-radius:14px;padding:18px;box-shadow:0 16px 46px #000b}.join h2,.lobbyBox h2{margin:0 0 14px;color:#ffe7a0}.join input{width:100%;padding:12px;border:1px solid #c8ad78;border-radius:9px;background:#fffdf0;font-size:18px}.btn{border:0;border-radius:9px;padding:10px 16px;margin:8px 5px 0 0;background:#28484a;color:#fff;cursor:pointer}.gold{background:linear-gradient(#d7a94c,#93621d)}.red{background:linear-gradient(#b8493e,#84221d)}.btn:disabled{opacity:.42;cursor:not-allowed}.seat{position:absolute;z-index:3;width:150px;text-align:center;color:#f9e8a9}.avatar{width:72px;height:72px;margin:auto;border-radius:12px;background:linear-gradient(135deg,#f7c16a,#8e372f);border:3px solid #34302b;display:grid;place-items:center;font-size:34px;box-shadow:0 8px 18px #0008}.active .avatar{border-color:#ffd25a;box-shadow:0 0 22px #ffd25a}.seatName{margin:3px auto 0;padding:3px 8px;width:max-content;max-width:150px;border-radius:5px;background:#071515cc;color:#ffe484;font-weight:800}.seatMeta{font-size:12px;color:#d7d6c6}.me{left:42px;bottom:110px}.right{right:40px;top:38%;transform:translateY(-50%)}.top{left:50%;top:16px;transform:translateX(-50%)}.left{left:42px;top:38%;transform:translateY(-50%)}.backs{position:absolute;display:flex;gap:3px;z-index:2}.backs.topBack{top:22px;left:50%;transform:translateX(-50%)}.backs.leftBack{left:210px;top:25%;flex-direction:column}.backs.rightBack{right:210px;top:25%;flex-direction:column}.back{width:38px;height:54px;border-radius:5px;background:linear-gradient(90deg,#eef4e7 0 18%,#45ad28 19% 100%);border:1px solid #165814;box-shadow:2px 2px 4px #0005}.leftBack .back,.rightBack .back{width:18px;height:42px}.center{position:absolute;left:50%;top:45%;transform:translate(-50%,-50%);z-index:4;width:150px;height:150px;border-radius:18px;background:linear-gradient(135deg,#111,#333);box-shadow:0 10px 24px #000b,inset 0 0 24px #000;border:2px solid #4a4a4a;display:grid;place-items:center}.wind{position:absolute;color:#ddd;font-size:28px;font-weight:900;text-shadow:0 2px 4px #000}.w0{bottom:9px;color:#8cff7e}.w1{right:15px}.w2{top:9px}.w3{left:15px}.timer{font-family:Consolas,monospace;font-size:58px;color:#cfe9ff;text-shadow:0 0 12px #64bcff}.turnGlow{position:absolute;inset:-8px;border-radius:24px;border:8px solid transparent}.turn0{border-bottom-color:#78ff66}.turn1{border-right-color:#78ff66}.turn2{border-top-color:#78ff66}.turn3{border-left-color:#78ff66}.wallCount{position:absolute;left:calc(50% + 95px);top:45%;transform:translateY(-50%);background:#46a92f;border:2px solid #246c20;border-radius:6px;padding:8px 10px;font-weight:900;box-shadow:0 5px 8px #0008}.dragonBox{position:absolute;left:calc(50% - 300px);top:45%;transform:translateY(-50%);display:flex;align-items:center;gap:10px;background:#123b42c9;border:1px solid #74a09c;border-radius:9px;padding:9px 12px;color:#fff}.lastShow{position:absolute;left:50%;top:31%;transform:translate(-50%,-50%);z-index:8;text-align:center;color:#ffe9aa;font-weight:900;min-height:98px}.lastShow .tile{animation:popIn .35s ease-out}.prompt{position:absolute;left:50%;bottom:178px;transform:translateX(-50%);z-index:8;background:#15263bcc;color:white;font-size:28px;padding:10px 34px;border-radius:4px;box-shadow:0 4px 14px #0007}.claimBar{position:absolute;left:50%;bottom:122px;transform:translateX(-50%);z-index:18;display:flex;gap:10px;align-items:center;justify-content:center}.claimBtn{min-width:64px;border:0;border-radius:999px;padding:12px 18px;background:linear-gradient(#ffe57b,#d58b1c);color:#712400;font-weight:900;font-size:24px;box-shadow:0 0 18px #ffd35e;text-shadow:0 1px #fff}.claimBtn.pass{background:linear-gradient(#f2f2e6,#89866d);color:#2b2b24}.claimHint{padding:10px 14px;border-radius:8px;background:#102e31e6;color:#ffe9aa;font-weight:800}.hand{position:absolute;left:50%;bottom:18px;transform:translateX(-50%);z-index:7;display:flex;gap:5px;max-width:82vw;justify-content:center}.tile{position:relative;width:58px;height:82px;border:2px solid #a9a083;border-radius:7px;background:linear-gradient(#fffff7,#eee8d2 54%,#d7cfb6);box-shadow:0 5px 0 #5f9637,3px 6px 10px #0008;color:#111;display:flex;align-items:center;justify-content:center;overflow:hidden}.tile.big{width:74px;height:102px}.tile.river{width:46px;height:64px;box-shadow:0 4px 0 #63893d,2px 5px 9px #0008}.tile.side{width:46px;height:64px;box-shadow:0 4px 0 #63893d,2px 5px 9px #0008}.tile[disabled]{filter:grayscale(.2);opacity:.65}.tile.dragonTile{background:linear-gradient(#fff7c8,#ebcb69)}.face{position:relative;z-index:1;display:grid;place-items:center}.mahjongGlyph{position:relative;z-index:1;font-size:48px;line-height:1;font-family:"Segoe UI Symbol","Noto Sans Symbols2",serif}.river .mahjongGlyph{font-size:30px}.side .mahjongGlyph{font-size:24px}.char{font-family:KaiTi,"STKaiti",serif;font-size:42px;font-weight:900;line-height:.8}.river .char{font-size:24px}.side .char{font-size:20px}.wan .char{color:#b51618}.honor .char{color:#111}.honor.red .char,.dragonText{color:#bd1515}.bamboo,.dotGrid{display:grid;gap:3px}.dotGrid{grid-template-columns:repeat(3,12px);grid-auto-rows:12px}.river .dotGrid{grid-template-columns:repeat(3,6px);grid-auto-rows:6px}.dot{border:2px solid #136d43;border-radius:50%;background:radial-gradient(circle,#d9282d 0 25%,#fff 27% 45%,#17935a 47% 100%)}.bamboo{grid-template-columns:repeat(3,7px);grid-auto-rows:18px}.river .bamboo{grid-template-columns:repeat(3,3px);grid-auto-rows:9px}.bam{border-radius:8px;background:linear-gradient(90deg,#0c7d42,#58bf74,#0c7d42)}.riverArea{position:absolute;z-index:5;display:grid;gap:6px}.river0{left:38%;bottom:34%;transform:translateX(-50%);grid-template-columns:repeat(6,46px)}.river2{left:50%;top:10%;transform:translateX(-50%);grid-template-columns:repeat(6,46px)}.river1{right:33%;top:24%;transform:none;grid-template-columns:repeat(4,46px)}.river3{left:27%;top:28%;transform:none;grid-template-columns:repeat(4,46px)}.sideMenu{position:absolute;right:18px;top:22px;z-index:12;width:110px;text-align:center}.huFloat{position:absolute;left:50%;bottom:128px;transform:translateX(-50%);z-index:16;width:78px;height:78px;border-radius:50%;display:grid;place-items:center;background:radial-gradient(circle,#fff6a6 0,#d99423 58%,#8f4811 100%);border:3px solid #ffe9a0;color:white;font-size:38px;font-family:KaiTi,"STKaiti",serif;font-weight:900;text-shadow:0 3px 4px #7a2500;box-shadow:0 0 22px #ffd35e;cursor:pointer}.roundBtn{width:78px;height:78px;margin:8px auto;border-radius:50%;border:3px solid #ffe9a0;background:radial-gradient(circle,#fff6a6 0,#d99423 58%,#8f4811 100%);color:white;font-weight:900;font-size:38px;font-family:KaiTi,"STKaiti",serif;text-shadow:0 3px 4px #7a2500;box-shadow:0 0 22px #ffd35e}.exitItem{display:flex;align-items:center;gap:8px;justify-content:center;margin-top:12px;font-size:24px;font-weight:900;color:#ffeec0;cursor:pointer}.exitItem:before{content:"←";font-size:44px}.logPanel{position:absolute;left:14px;bottom:12px;z-index:15;width:260px;max-height:150px;overflow:auto;background:#fff8e8e8;color:#2b2b24;border-radius:8px;padding:8px;font-size:12px}.lobbyCards{display:grid;grid-template-columns:repeat(2,1fr);gap:8px}.card{border:1px solid #8f7750;border-radius:8px;padding:9px;background:#fff8e8;color:#222}@keyframes popIn{0%{transform:translateY(-34px) scale(.65);opacity:0}65%{transform:translateY(4px) scale(1.12)}100%{transform:translateY(0) scale(1);opacity:1}}@media(max-width:820px){.game{overflow:auto}.tile{width:43px;height:62px}.hand{max-width:96vw}.seat{width:110px}.avatar{width:52px;height:52px}.backs.leftBack,.backs.rightBack{display:none}.river1{right:120px}.river3{left:120px}.sideMenu{right:6px}.logPanel{display:none}.prompt{font-size:18px;bottom:145px}.center{width:112px;height:112px}.timer{font-size:42px}}
.tileFace{position:relative;z-index:1;width:100%;height:100%;display:grid;place-items:center;padding:8px 6px 10px}.wanFace{font-family:KaiTi,"STKaiti",serif;font-weight:900;color:#b51616;text-align:center;line-height:.78}.wanFace .top{position:static;transform:none;font-size:32px;display:block}.wanFace .bottom{font-size:22px;display:block;margin-top:4px}.honorFace{font-family:KaiTi,"STKaiti",serif;font-size:40px;font-weight:900;line-height:1;color:#111}.honorFace.red{color:#b51616}.tongGrid{display:grid;grid-template-columns:repeat(3,13px);grid-auto-rows:13px;gap:3px}.tongDot{border:2px solid #243a68;border-radius:50%;background:radial-gradient(circle,#c92a2a 0 23%,#fff 25% 43%,#2d4172 45% 100%)}.tiaoGrid{display:grid;grid-template-columns:repeat(3,8px);grid-auto-rows:17px;gap:3px}.tiaoStick{border-radius:8px;background:linear-gradient(90deg,#0d642e,#4fab5a 45%,#0d642e);border:1px solid #095024}.bird{font-size:36px;color:#0f6a35;text-shadow:0 1px #fff}.river .tileFace{padding:4px 3px 5px}.river .wanFace .top{font-size:18px}.river .wanFace .bottom{font-size:13px;margin-top:2px}.river .honorFace{font-size:24px}.river .tongGrid{grid-template-columns:repeat(3,7px);grid-auto-rows:7px;gap:1px}.river .tongDot{border-width:1px}.river .tiaoGrid{grid-template-columns:repeat(3,4px);grid-auto-rows:8px;gap:1px}.river .bird{font-size:20px}.side .tileFace{padding:4px 3px 5px}.side .wanFace .top{font-size:18px}.side .wanFace .bottom{font-size:13px;margin-top:2px}.side .honorFace{font-size:24px}.side .tongGrid{grid-template-columns:repeat(3,7px);grid-auto-rows:7px;gap:1px}.side .tongDot{border-width:1px}.side .tiaoGrid{grid-template-columns:repeat(3,4px);grid-auto-rows:8px;gap:1px}.side .bird{font-size:20px}.tileSvg{position:relative;z-index:2;width:100%;height:100%;display:block}.tile:before{background:#fffdf7}.river .tileSvg,.side .tileSvg{width:100%;height:100%}.hand .tile{transition:transform .12s ease,box-shadow .12s ease}.hand .tile.selected{transform:translateY(-28px);box-shadow:0 8px 0 #4a7b2b,0 0 0 4px #ffd35e,3px 12px 18px #000b;z-index:20}.settlement{margin:0 0 12px;padding:10px;border:1px solid #d6b56f;border-radius:10px;background:#071d1de8;color:#fff2c5}.settleHead{font-size:18px;font-weight:900;color:#ffe484;margin-bottom:4px}.settleMeta{font-size:13px;line-height:1.45;color:#f6e7bb}.settlePlayers{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:8px;margin-top:10px}.settlePlayer{border:1px solid #90794f;border-radius:8px;background:#fff8e8;color:#222;padding:8px;min-width:0}.settlePlayer.win{border-color:#ffd35e;box-shadow:0 0 12px #ffd35e80}.settleName{font-weight:900;margin-bottom:5px}.settleTags{float:right;color:#9a261e;font-weight:900}.settleTiles{display:flex;flex-wrap:wrap;gap:3px;margin:4px 0;min-height:36px}.settleTiles .tile{width:32px;height:46px;border-radius:4px;box-shadow:0 3px 0 #63893d,1px 3px 5px #0006}.settleLabel{font-size:12px;color:#675b45;margin-top:5px}.deltaPlus{color:#11712a;font-weight:900}.deltaMinus{color:#b51616;font-weight:900}@media(max-width:820px){.settlePlayers{grid-template-columns:1fr}.settlement{max-height:54vh;overflow:auto}.settleTiles .tile{width:28px;height:40px}}@media(orientation:landscape) and (max-height:560px) and (hover:none) and (pointer:coarse){body{min-height:100dvh}.game{height:100dvh;min-height:100dvh;overflow:hidden;padding:env(safe-area-inset-top) env(safe-area-inset-right) env(safe-area-inset-bottom) env(safe-area-inset-left)}.game:before{inset:11% 19%}.topbar{left:8px;top:6px;gap:6px}.brand{padding:5px 8px;border-radius:9px;font-size:12px}.round{font-size:11px;max-width:46vw;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.join,.lobbyBox{width:min(620px,88vw);max-height:88dvh;overflow:auto;padding:12px;border-radius:11px}.join h2,.lobbyBox h2{font-size:18px;margin-bottom:8px}.lobbyCards{grid-template-columns:repeat(4,minmax(0,1fr));gap:6px}.card{padding:6px;font-size:12px}.btn{padding:8px 12px;margin-top:6px;font-size:14px}.seat{width:92px}.avatar{width:46px;height:46px;border-radius:9px;font-size:24px}.seatName{font-size:12px;padding:2px 6px;max-width:92px}.seatMeta{font-size:10px;line-height:1.15}.me{left:18px;bottom:62px}.left{left:16px;top:47%}.right{right:16px;top:47%}.top{top:4px}.backs.topBack{top:12px;left:50%;gap:2px}.backs.leftBack{left:118px;top:24%;gap:2px}.backs.rightBack{right:118px;top:24%;gap:2px}.back{width:30px;height:40px;border-radius:4px}.leftBack .back,.rightBack .back{width:13px;height:31px}.center{width:94px;height:94px;top:43%;border-radius:14px}.timer{font-size:36px}.wind{font-size:18px}.w0{bottom:6px}.w1{right:8px}.w2{top:6px}.w3{left:8px}.wallCount{left:calc(50% + 64px);top:43%;padding:5px 7px;font-size:13px}.dragonBox{left:calc(50% - 210px);top:43%;padding:5px 7px;gap:5px;font-size:12px}.dragonBox .tile{width:32px;height:44px}.lastShow{top:27%;min-height:68px;font-size:12px}.lastShow .tile.big{width:46px;height:64px}.prompt{bottom:82px;font-size:16px;padding:6px 16px;border-radius:6px}.claimBar{bottom:74px;gap:6px}.claimBtn{min-width:50px;padding:9px 13px;font-size:18px}.claimHint{padding:7px 9px;font-size:12px}.huFloat{bottom:78px;width:56px;height:56px;font-size:28px}.hand{bottom:6px;gap:3px;max-width:76vw}.hand .tile{width:min(42px,6.1vw);height:min(59px,8.6vw);border-radius:5px}.hand .tile.selected{transform:translateY(-19px)}.tile.river,.tile.side{width:31px;height:43px;border-radius:4px}.riverArea{gap:3px}.river0{left:39%;bottom:30%;grid-template-columns:repeat(6,31px)}.river2{left:50%;top:12%;grid-template-columns:repeat(6,31px)}.river1{right:27%;top:27%;grid-template-columns:repeat(4,31px)}.river3{left:27%;top:31%;grid-template-columns:repeat(4,31px)}.sideMenu{right:7px;top:8px;width:72px}.exitItem{font-size:16px;margin-top:4px}.exitItem:before{font-size:28px}.logPanel{display:none}.settlement{max-height:56dvh;overflow:auto;padding:8px;margin-bottom:8px}.settleHead{font-size:16px}.settleMeta{font-size:12px}.settlePlayers{grid-template-columns:repeat(2,minmax(0,1fr));gap:6px}.settlePlayer{padding:6px}.settleTiles .tile{width:27px;height:38px}.settleLabel{font-size:11px;margin-top:3px}}@media(orientation:landscape) and (max-height:430px) and (hover:none) and (pointer:coarse){.brand{font-size:11px}.round{display:none}.avatar{width:40px;height:40px}.seat{width:82px}.seatName{font-size:11px;max-width:82px}.seatMeta{font-size:9px}.center{width:82px;height:82px}.timer{font-size:30px}.hand .tile{width:min(36px,5.5vw);height:min(51px,7.8vw)}.tile.river,.tile.side{width:27px;height:38px}.river0{grid-template-columns:repeat(6,27px)}.river2{grid-template-columns:repeat(6,27px)}.river1,.river3{grid-template-columns:repeat(4,27px)}.prompt{font-size:14px;bottom:68px}.claimBar{bottom:60px}.huFloat{bottom:64px}}</style><div class="game"><div id="join" class="join"><h2>小马识途麻将</h2><input id="name" placeholder="你的名字"><button class="btn gold" onclick="join()">入座</button><p>把当前网址发给朋友，朋友点击即可进入同一房间。</p></div><div id="game" class="hide"><div class="topbar"><div class="brand">余姚瞎子麻将</div><div class="round" id="topInfo">等待开局</div></div><div id="lobby" class="lobbyBox"><h2 id="lobbyTitle">等待准备</h2><div id="settlement" class="settlement hide"></div><div id="lobbyPlayers" class="lobbyCards"></div><button id="readyBtn" class="btn gold" onclick="ready()">准备</button><button id="startBtn" class="btn gold" onclick="startGame()">房主开始</button><button class="btn red" onclick="leaveSeat()">退出游戏</button></div><div id="s0" class="seat me"></div><div id="s1" class="seat right"></div><div id="s2" class="seat top"></div><div id="s3" class="seat left"></div><div id="b1" class="backs rightBack"></div><div id="b2" class="backs topBack"></div><div id="b3" class="backs leftBack"></div><div class="center"><div id="turnGlow" class="turnGlow turn0"></div><div class="wind w0">东</div><div class="wind w1">南</div><div class="wind w2">西</div><div class="wind w3">北</div><div id="timer" class="timer">30</div></div><div id="wall" class="wallCount">0</div><div class="dragonBox"><div id="dragonTile"></div><span id="dragonName">龙牌</span></div><div id="lastShow" class="lastShow"></div><div id="prompt" class="prompt hide"></div><div id="claimBar" class="claimBar hide"></div><div id="huFloat" class="huFloat hide" onclick="hu()">胡</div><div id="p0" class="riverArea river0"></div><div id="p1" class="riverArea river1"></div><div id="p2" class="riverArea river2"></div><div id="p3" class="riverArea river3"></div><div id="hand" class="hand"></div><div class="sideMenu"><div class="exitItem" onclick="leaveSeat()">退出</div></div><div class="logPanel"><b>流水</b><div id="log"></div></div></div></div><script>
const room=location.pathname.split('/').filter(Boolean).pop()||'';let key='xmst_'+room,saved=JSON.parse(localStorage.getItem(key)||'{}'),seat=saved.seat??-1,token=saved.token||'',lastKey='',selectedTile=-1;
async function post(a,d){return fetch(a,{method:'POST',headers:{'Content-Type':'application/x-www-form-urlencoded'},body:new URLSearchParams(d)}).then(r=>r.json())}
async function join(){let r=await post('/api/join/'+room,{name:document.getElementById('name').value||'好友',token});if(r.ok){seat=r.seat;token=r.token;localStorage.setItem(key,JSON.stringify({seat,token}));tick()}else alert(r.error)}
async function act(a,d={}){let r=await post('/api/'+a+'/'+room,{seat,token,...d});if(!r.ok&&r.error)alert(r.error);setTimeout(tick,120)}
async function chooseDiscard(i){if(!S||!S.canAct)return;if(selectedTile!==i){selectedTile=i;render(S);return}selectedTile=-1;await act('discard',{pos:i})}async function discard(i){await chooseDiscard(i)}async function ready(){await act('ready')}async function startGame(){selectedTile=-1;await act('start')}async function leaveSeat(){await act('leave');localStorage.removeItem(key);seat=-1;token='';selectedTile=-1;tick()}async function hu(){await act('hu')}async function peng(){await act('peng')}async function gang(){await act('gang')}async function passClaim(){await act('pass')}
function rel(a,m){return(a-m+4)%4}function suit(id){return id<9?'wan':id<18?'tong':id<27?'tiao':'honor'}function num(id){return id%9+1}
const tileBase='https://cdn.jsdelivr.net/gh/samoheen/mahjong-tiles@master/hongkong/svg/';
function tileFile(id){if(id<9)return String(id+8).padStart(2,'0')+'-characters-'+(id+1)+'.svg';if(id<18)return String(id+8).padStart(2,'0')+'-circles-'+(id-8)+'.svg';if(id<27)return String(id+8).padStart(2,'0')+'-bamboos-'+(id-17)+'.svg';return ['04-east-wind.svg','05-south-wind.svg','06-west-wind.svg','07-north-wind.svg','03-red-dragon.svg','02-green-dragon.svg','01-white-dragon.svg'][id-27]}
function tileInner(x){return `<img src="${tileBase+tileFile(x.id)}" alt="${x.name}" style="position:relative;z-index:2;width:100%;height:100%;object-fit:contain;display:block;pointer-events:none">`}
function tile(x,cls='',dis=false){if(!x)return'';let id=x.id,k=suit(id);return `<button class="tile ${cls} ${k} ${id==S?.dragonId?'dragonTile':''}" ${dis?'disabled':''} title="${x.name}">${tileInner(x)}</button>`}let S=null;function esc(x){return String(x??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]))}function deltaText(n){return `<span class="${n>=0?'deltaPlus':'deltaMinus'}">${n>=0?'+':''}${n}分</span>`}function renderSettlement(s){let box=document.getElementById('settlement'),title=document.getElementById('lobbyTitle'),r=s.roundReveal;if(!r){box.classList.add('hide');box.innerHTML='';title.textContent='等待准备';return}title.textContent='本局结算';let players=[...r.players].sort((a,b)=>rel(a.seat,s.seat)-rel(b.seat,s.seat));let names=[...(r.baseTypes||[]),...(r.patterns||[])].join('、')||'未识别';box.innerHTML=`<div class="settleHead">${esc(r.winner)} ${esc(r.method)}胡 ${r.dragons}龙</div><div class="settleMeta">胡牌：${r.winningTile?esc(r.winningTile.name):'无'} · 龙牌：${r.dragon?esc(r.dragon.name):'无'} · 牌型：${esc(names)}<br>${esc(r.payText||'')}</div><div class="settlePlayers">${players.map(p=>{let tags=(p.winner?'赢家 ':'')+(p.discarder?'点炮 ':'')+(p.seat==s.seat?'我 ':'');let melds=(p.melds||[]).map(m=>tile(m.tile,'',true)).join('');return `<div class="settlePlayer ${p.winner?'win':''}"><div class="settleName">${esc(p.name)} <span class="settleTags">${esc(tags)}</span><br>${deltaText(p.delta)} · 总分 ${p.score}</div><div class="settleLabel">手牌</div><div class="settleTiles">${(p.hand||[]).map(x=>tile(x,'',true)).join('')}</div>${melds?`<div class="settleLabel">碰杠</div><div class="settleTiles">${melds}</div>`:''}<div class="settleLabel">打出</div><div class="settleTiles">${(p.discards||[]).map(x=>tile(x,'',true)).join('')}</div></div>`}).join('')}</div>`;box.classList.remove('hide')}function renderSeats(s){for(let i=0;i<4;i++){document.getElementById('s'+i).innerHTML='';document.getElementById('p'+i).innerHTML=''}s.players.forEach(p=>{let r=rel(p.seat,s.seat),flag=(p.owner?'房主 ':'')+(p.human?(p.ready?'已准备':'未准备'):'电脑补位'),act=p.seat==s.currentSeat?' active':'';let el=document.getElementById('s'+r);el.className=el.className.replace(' active','')+act;el.innerHTML=`<div class="avatar">${p.human?'马':'机'}</div><div class="seatName">${p.name}${p.seat==s.seat?'（我）':''}</div><div class="seatMeta">${flag} · ${p.handCount}张 · ${p.score}分</div>`;document.getElementById('p'+r).innerHTML=p.discards.map(x=>tile(x,(r==1||r==3)?'side':'river')).join('')});for(let r=1;r<=3;r++){let p=s.players.find(x=>rel(x.seat,s.seat)==r),n=p?Math.max(0,p.handCount):0;document.getElementById('b'+r).innerHTML=Array.from({length:n},()=>'<i class="back"></i>').join('')}}
function render(s){S=s;if(!s.canAct||selectedTile>=s.hand.length)selectedTile=-1;renderSeats(s);renderSettlement(s);document.getElementById('lobby').classList.toggle('hide',s.phase!='lobby');document.getElementById('lobbyPlayers').innerHTML=s.players.map(p=>`<div class="card"><b>${p.name}${p.seat==s.seat?'（我）':''}</b><br>${p.human?(p.ready?'已准备':'未准备'):'电脑补位'}${p.owner?' · 房主':''}<br>${p.score}分</div>`).join('');document.getElementById('readyBtn').disabled=!s.canReady;document.getElementById('readyBtn').textContent=s.ready?'取消准备':'准备';document.getElementById('startBtn').disabled=!s.canStart;document.getElementById('timer').textContent=s.remaining;document.getElementById('wall').textContent=s.wall;document.getElementById('topInfo').textContent=s.phase=='lobby'?'房间 '+s.room+' · 等待准备':`房间 ${s.room} · ${s.current} 出牌 · 龙牌 ${s.dragon}`;document.getElementById('turnGlow').className='turnGlow turn'+rel(s.currentSeat,s.seat);document.getElementById('dragonTile').innerHTML=s.phase=='playing'?tile({id:s.dragonId,name:s.dragon},'river'):'';document.getElementById('dragonName').textContent=s.phase=='playing'?'龙牌 '+s.dragon:'未开局';document.getElementById('hand').innerHTML=s.hand.map((x,i)=>`<button class="tile ${suit(x.id)} ${x.id==s.dragonId?'dragonTile':''} ${selectedTile==i?'selected':''}" ${s.canAct?'':'disabled'} onclick="discard(${i})">${tileInner(x)}</button>`).join('');let p=document.getElementById('prompt');p.classList.toggle('hide',s.phase!='playing');let claiming=s.claimTile&&(s.canHu||s.canPeng||s.canGang);p.textContent=claiming?`有人打出 ${s.claimTile.name}，剩 ${s.claimDeadline} 秒`:s.canAct?(selectedTile>=0?'再点一次打出这张':'轮到你出牌'):`${s.current} 正在出牌`;let lk=s.lastDiscard?(s.lastDiscarder+'-'+s.lastDiscard.name+'-'+s.players[s.lastDiscarder]?.discards.length):'';if(s.lastDiscard&&lk!==lastKey){lastKey=lk;document.getElementById('lastShow').innerHTML='<div>'+s.lastDiscarderName+' 打出</div>'+tile(s.lastDiscard,'big')}let cb=document.getElementById('claimBar'),btns=[];if(s.canHu)btns.push(`<button class="claimBtn" onclick="hu()">胡</button>`);if(s.canGang)btns.push(`<button class="claimBtn" onclick="gang()">杠</button>`);if(s.canPeng)btns.push(`<button class="claimBtn" onclick="peng()">碰</button>`);if(claiming)btns.push(`<button class="claimBtn pass" onclick="passClaim()">过</button><span class="claimHint">${(s.winTypes||[]).join('、')}</span>`);cb.innerHTML=btns.join('');cb.classList.toggle('hide',btns.length==0);document.getElementById('huFloat').classList.toggle('hide',!(s.canHu&&!claiming));document.getElementById('log').innerHTML=s.log.join('<br>')}
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
   elif action=='peng': r.claim_peng(seat)
   elif action=='gang': r.claim_gang(seat) if r.claim else r.gang(seat)
   elif action=='pass': r.pass_claim(seat)
   elif action=='hu': r.hu(seat)
   self.js({'ok':True})
  except Exception as e: self.js({'ok':False,'error':str(e)})
def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--host',default='0.0.0.0'); ap.add_argument('--port',type=int,default=int(os.environ.get('PORT','8000'))); a=ap.parse_args(); ThreadingHTTPServer((a.host,a.port),H).serve_forever()
if __name__=='__main__': main()













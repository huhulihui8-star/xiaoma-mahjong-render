import argparse
import json
import os
import random
import secrets
import string
import threading
import time
from dataclasses import dataclass, field
from functools import lru_cache
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse


HONORS = ["东", "南", "西", "北", "中", "发", "白"]
DEFAULT_NAMES = ["南家", "下家", "对家", "上家"]


def build_tile_names():
    names = []
    for suit in ("万", "筒", "条"):
        for n in range(1, 10):
            names.append(f"{n}{suit}")
    names.extend(HONORS)
    return names


TILE_NAMES = build_tile_names()


def next_dragon(indicator_id):
    if indicator_id < 27:
        base = indicator_id // 9 * 9
        return base + ((indicator_id - base + 1) % 9)
    order = [27, 28, 29, 30, 31, 32, 33]
    return order[(order.index(indicator_id) + 1) % len(order)]


def counts_from_tiles(tiles):
    counts = [0] * 34
    for tile in tiles:
        counts[tile] += 1
    return counts


def can_win_with_wildcards(tiles, wild_id, exposed_melds=0):
    needed_melds = 4 - exposed_melds
    wilds = sum(1 for tile in tiles if tile == wild_id)
    counts = counts_from_tiles(tile for tile in tiles if tile != wild_id)
    if sum(counts) + wilds != needed_melds * 3 + 2:
        return False

    @lru_cache(maxsize=None)
    def meldable(state, wild_left, melds_left):
        state = list(state)
        if melds_left == 0:
            return sum(state) == 0
        first = next((i for i, c in enumerate(state) if c), None)
        if first is None:
            return wild_left >= melds_left * 3
        need = max(0, 3 - state[first])
        if need <= wild_left:
            used = min(3, state[first])
            state[first] -= used
            if meldable(tuple(state), wild_left - need, melds_left - 1):
                return True
            state[first] += used
        if first < 27 and first % 9 <= 6:
            need = 0
            used_tiles = []
            for offset in (0, 1, 2):
                idx = first + offset
                if state[idx]:
                    used_tiles.append(idx)
                else:
                    need += 1
            if need <= wild_left:
                for idx in used_tiles:
                    state[idx] -= 1
                if meldable(tuple(state), wild_left - need, melds_left - 1):
                    return True
                for idx in used_tiles:
                    state[idx] += 1
        return False

    for pair_id in range(34):
        need = max(0, 2 - counts[pair_id])
        if need <= wilds:
            pair_counts = counts[:]
            pair_counts[pair_id] -= min(2, pair_counts[pair_id])
            if meldable(tuple(pair_counts), wilds - need, needed_melds):
                return True
    return wilds >= 2 and meldable(tuple(counts), wilds - 2, needed_melds)


@dataclass
class Player:
    name: str
    human: bool = False
    token: str = ""
    hand: list = field(default_factory=list)
    melds: list = field(default_factory=list)
    discards: list = field(default_factory=list)
    score: int = 0


class Room:
    def __init__(self, room_id):
        self.room_id = room_id
        self.lock = threading.RLock()
        self.players = [Player(DEFAULT_NAMES[i]) for i in range(4)]
        self.wall = []
        self.indicator = 0
        self.dragon = 0
        self.current = 0
        self.dealer = 0
        self.last_discard = None
        self.last_discarder = None
        self.awaiting_claim = False
        self.player_must_discard = False
        self.log = []
        self.round_no = 1
        self.new_round()

    def add_log(self, text):
        self.log.append(text)
        self.log = self.log[-80:]

    def new_round(self):
        old_scores = [p.score for p in self.players]
        old_names = [p.name for p in self.players]
        old_humans = [p.human for p in self.players]
        old_tokens = [p.token for p in self.players]
        self.players = [
            Player(old_names[i], old_humans[i], old_tokens[i], score=old_scores[i])
            for i in range(4)
        ]
        self.wall = list(range(34)) * 4
        random.shuffle(self.wall)
        self.indicator = self.wall.pop()
        self.dragon = next_dragon(self.indicator)
        self.current = self.dealer
        self.last_discard = None
        self.last_discarder = None
        self.awaiting_claim = False
        self.player_must_discard = False
        for _ in range(13):
            for player in self.players:
                player.hand.append(self.wall.pop())
        self.players[self.dealer].hand.append(self.wall.pop())
        for player in self.players:
            player.hand.sort()
        self.player_must_discard = True
        self.add_log(f"第 {self.round_no} 局开始，庄家 {self.players[self.dealer].name}，龙牌 {TILE_NAMES[self.dragon]}。")
        self.round_no += 1

    def join(self, name, token=None):
        with self.lock:
            if token:
                for seat, player in enumerate(self.players):
                    if player.human and player.token == token:
                        return seat, player.token
            for seat, player in enumerate(self.players):
                if not player.human:
                    player.human = True
                    player.name = name[:10] or f"玩家{seat + 1}"
                    player.token = secrets.token_urlsafe(12)
                    self.add_log(f"{player.name} 加入房间。")
                    return seat, player.token
            raise ValueError("房间已满")

    def auth(self, seat, token):
        return 0 <= seat < 4 and self.players[seat].human and self.players[seat].token == token

    def draw_tile(self, seat):
        if not self.wall:
            self.add_log("牌墙摸完，流局。")
            self.dealer = (self.dealer + 1) % 4
            self.new_round()
            return None
        tile = self.wall.pop()
        self.players[seat].hand.append(tile)
        self.players[seat].hand.sort()
        return tile

    def choose_ai_discard(self, player):
        non_dragon = [t for t in player.hand if t != self.dragon]
        choices = non_dragon or player.hand[:]
        counts = counts_from_tiles(player.hand)
        choices.sort(key=lambda t: (counts[t], random.random()))
        return choices[0]

    def process_ai_until_human(self):
        with self.lock:
            guard = 0
            while guard < 60 and not self.awaiting_claim and not self.players[self.current].human:
                guard += 1
                player = self.players[self.current]
                if not self.player_must_discard:
                    self.draw_tile(self.current)
                    self.player_must_discard = True
                if can_win_with_wildcards(player.hand, self.dragon, len(player.melds)):
                    self.finish_win(self.current)
                    continue
                discard = self.choose_ai_discard(player)
                player.hand.remove(discard)
                player.discards.append(discard)
                self.last_discard = discard
                self.last_discarder = self.current
                self.player_must_discard = False
                self.add_log(f"{player.name} 打出 {TILE_NAMES[discard]}。")
                if self.offer_claim(discard):
                    return
                self.current = (self.current + 1) % 4
                if not self.players[self.current].human:
                    self.player_must_discard = False
                else:
                    self.player_must_discard = False
                    self.draw_tile(self.current)
                    self.player_must_discard = True

    def offer_claim(self, discard):
        for offset in range(1, 4):
            seat = (self.last_discarder + offset) % 4
            player = self.players[seat]
            if player.human and player.hand.count(discard) >= 2:
                self.awaiting_claim = True
                self.current = seat
                self.add_log(f"{player.name} 可以碰/杠 {TILE_NAMES[discard]}。")
                return True
        return False

    def discard(self, seat, pos):
        with self.lock:
            if not self.auth(seat, self.players[seat].token):
                return
            if self.current != seat or not self.player_must_discard or self.awaiting_claim:
                return
            player = self.players[seat]
            if pos < 0 or pos >= len(player.hand):
                return
            tile = player.hand.pop(pos)
            player.discards.append(tile)
            self.last_discard = tile
            self.last_discarder = seat
            self.player_must_discard = False
            self.add_log(f"{player.name} 打出 {TILE_NAMES[tile]}。")
            if not self.offer_claim(tile):
                self.current = (seat + 1) % 4
                if self.players[self.current].human:
                    self.draw_tile(self.current)
                    self.player_must_discard = True
                else:
                    self.player_must_discard = False
        self.process_ai_until_human()

    def claim(self, seat, count):
        with self.lock:
            if not self.awaiting_claim or self.current != seat or self.last_discard is None:
                return
            player = self.players[seat]
            if player.hand.count(self.last_discard) < count:
                return
            for _ in range(count):
                player.hand.remove(self.last_discard)
            player.melds.append([self.last_discard] * (count + 1))
            self.awaiting_claim = False
            self.player_must_discard = True
            self.add_log(f"{player.name}{'杠' if count == 3 else '碰'}了 {TILE_NAMES[self.last_discard]}。")
            if count == 3:
                self.draw_tile(seat)

    def pass_claim(self, seat):
        with self.lock:
            if self.awaiting_claim and self.current == seat:
                self.awaiting_claim = False
                self.current = (self.last_discarder + 1) % 4
                if self.players[self.current].human:
                    self.draw_tile(self.current)
                    self.player_must_discard = True
                else:
                    self.player_must_discard = False
                self.add_log(f"{self.players[seat].name} 选择过。")
        self.process_ai_until_human()

    def hu(self, seat):
        with self.lock:
            if self.current == seat and can_win_with_wildcards(self.players[seat].hand, self.dragon, len(self.players[seat].melds)):
                self.finish_win(seat)

    def finish_win(self, winner):
        base = 10
        for idx, player in enumerate(self.players):
            if idx != winner:
                player.score -= base
                self.players[winner].score += base
        self.add_log(f"{self.players[winner].name} 自摸胡，三家各付 {base} 分。")
        self.dealer = winner if winner == self.dealer else (self.dealer + 1) % 4
        self.new_round()

    def state(self, seat):
        with self.lock:
            self.process_ai_until_human()
            player = self.players[seat]
            same_count = player.hand.count(self.last_discard) if self.last_discard is not None else 0
            return {
                "room": self.room_id,
                "seat": seat,
                "name": player.name,
                "current": self.players[self.current].name,
                "wall": len(self.wall),
                "dragon": TILE_NAMES[self.dragon],
                "dragonId": self.dragon,
                "canAct": self.current == seat and self.player_must_discard and not self.awaiting_claim,
                "canClaim": self.current == seat and self.awaiting_claim and same_count >= 2,
                "canKong": self.current == seat and self.awaiting_claim and same_count >= 3,
                "hand": [{"id": t, "name": TILE_NAMES[t]} for t in player.hand],
                "players": [
                    {
                        "seat": i,
                        "name": p.name,
                        "human": p.human,
                        "score": p.score,
                        "handCount": len(p.hand),
                        "discards": [{"id": t, "name": TILE_NAMES[t]} for t in p.discards[-24:]],
                    }
                    for i, p in enumerate(self.players)
                ],
                "log": self.log[-16:],
            }


ROOMS = {}
ROOM_LOCK = threading.RLock()


def new_room_id():
    alphabet = string.ascii_uppercase + string.digits
    return "".join(secrets.choice(alphabet) for _ in range(6))


def get_or_create_room(room_id=None):
    with ROOM_LOCK:
        if not room_id:
            room_id = new_room_id()
        if room_id not in ROOMS:
            ROOMS[room_id] = Room(room_id)
        return ROOMS[room_id]


HTML = r"""<!doctype html>
<html lang="zh-CN">
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>小马识途麻将云服务器版</title>
<style>
body{margin:0;font-family:"Microsoft YaHei",Arial,sans-serif;background:#f4efe5;color:#263238}
header{background:#263238;color:#fff8e7;padding:12px 14px;font-size:22px;font-weight:700}
main{padding:10px}.panel{background:#fffaf0;border:1px solid #d8c6a7;border-radius:8px;padding:10px;margin:8px 0}
.btn{padding:10px 14px;margin:4px;border:0;border-radius:6px;background:#263238;color:white;font-size:15px}.bar{margin:8px 0;color:#5a4f43}
.hand{display:flex;flex-wrap:wrap;gap:6px}.tile{width:46px;height:64px;border:2px solid #6e6256;border-radius:7px;background:#fffdf7;box-shadow:2px 3px 0 #b29d83;font-weight:700;font-size:16px}
.riverTile{width:34px;height:48px;font-size:13px}.sideTile{width:48px;height:34px;font-size:13px}.dragon{background:#ffe7a6;border-color:#b68f4f}
.table{position:relative;height:430px;background:#d8c6a7;border:2px solid #9a805d;border-radius:12px;overflow:hidden;margin:8px 0}.center{position:absolute;left:50%;top:50%;width:180px;height:96px;transform:translate(-50%,-50%);background:#b99d73;border:2px solid #8c7354;border-radius:10px;display:flex;align-items:center;justify-content:center;font-weight:700;color:#5b4630}
.seat{position:absolute;font-weight:700;color:#263238;background:rgba(255,250,240,.75);padding:4px 8px;border-radius:6px}.bottomName{left:50%;bottom:8px;transform:translateX(-50%)}.topName{left:50%;top:8px;transform:translateX(-50%)}.rightName{right:8px;top:50%;transform:translateY(-50%)}.leftName{left:8px;top:50%;transform:translateY(-50%)}
.pile{position:absolute;display:grid;gap:4px}.bottomPile{left:50%;bottom:60px;transform:translateX(-50%);grid-template-columns:repeat(8,34px)}.topPile{left:50%;top:58px;transform:translateX(-50%);grid-template-columns:repeat(8,34px);direction:rtl}.rightPile{right:58px;top:50%;transform:translateY(-50%);grid-template-columns:repeat(3,48px)}.leftPile{left:58px;top:50%;transform:translateY(-50%);grid-template-columns:repeat(3,48px)}
input{font-size:16px;padding:8px;width:150px}.small{font-size:13px;color:#6b6257}
</style>
<header>小马识途麻将</header>
<main>
<div id="join" class="panel"><b>加入云端房间</b><div style="margin-top:8px"><input id="name" placeholder="你的名字"><button class="btn" onclick="join()">入座</button></div><div class="small">把当前网址发给朋友即可加入同一房间。</div></div>
<div id="game" style="display:none">
  <div class="panel"><b id="seat"></b><div id="info" class="bar"></div><button class="btn" onclick="hu()">自摸胡</button><button class="btn" onclick="pong()">碰</button><button class="btn" onclick="kong()">杠</button><button class="btn" onclick="passTurn()">过</button></div>
  <div class="table"><div class="center">小马识途麻将</div><div id="name0" class="seat bottomName"></div><div id="name1" class="seat rightName"></div><div id="name2" class="seat topName"></div><div id="name3" class="seat leftName"></div><div id="pile0" class="pile bottomPile"></div><div id="pile1" class="pile rightPile"></div><div id="pile2" class="pile topPile"></div><div id="pile3" class="pile leftPile"></div></div>
  <div class="panel"><b>我的手牌</b><div id="hand" class="hand"></div><div class="small">轮到你时，点牌即可打出。</div></div>
  <div class="panel"><b>流水</b><div id="log" class="small"></div></div>
</div>
<script>
const room=location.pathname.split('/').filter(Boolean).pop()||'';
let key='xmst_'+room, saved=JSON.parse(localStorage.getItem(key)||'{}'), seat=saved.seat??-1, token=saved.token||'';
async function post(path,data){return fetch(path,{method:'POST',headers:{'Content-Type':'application/x-www-form-urlencoded'},body:new URLSearchParams(data)}).then(r=>r.json())}
async function join(){let name=document.getElementById('name').value||'好友';let r=await post('/api/join/'+room,{name,token});if(r.ok){seat=r.seat;token=r.token;localStorage.setItem(key,JSON.stringify({seat,token}));tick()}else alert(r.error)}
async function discard(pos){await post('/api/discard/'+room,{seat,token,pos});setTimeout(tick,120)}
async function hu(){await post('/api/hu/'+room,{seat,token});setTimeout(tick,120)}
async function pong(){await post('/api/pong/'+room,{seat,token});setTimeout(tick,120)}
async function kong(){await post('/api/kong/'+room,{seat,token});setTimeout(tick,120)}
async function passTurn(){await post('/api/pass/'+room,{seat,token});setTimeout(tick,120)}
function rel(abs,my){return (abs-my+4)%4}
function renderTable(s){for(let i=0;i<4;i++){document.getElementById('pile'+i).innerHTML='';document.getElementById('name'+i).textContent=''};s.players.forEach(p=>{let r=rel(p.seat,s.seat);document.getElementById('name'+r).textContent=p.name+(p.seat==s.seat?'（我）':p.human?'':'（电脑）');document.getElementById('pile'+r).innerHTML=p.discards.map(x=>`<button class="${(r==1||r==3)?'tile sideTile':'tile riverTile'} ${x.id==s.dragonId?'dragon':''}">${x.name}</button>`).join('')})}
async function tick(){if(seat<0||!token){document.getElementById('join').style.display='block';return}let s=await fetch('/api/state/'+room+'?seat='+seat+'&token='+encodeURIComponent(token)).then(r=>r.json());if(!s.ok){document.getElementById('join').style.display='block';document.getElementById('game').style.display='none';return}document.getElementById('join').style.display='none';document.getElementById('game').style.display='block';document.getElementById('seat').textContent=s.name+'（房间 '+s.room+'）';document.getElementById('info').textContent=`当前：${s.current}　剩余：${s.wall}　龙牌：${s.dragon}　${s.canAct?'轮到你出牌':(s.canClaim?'你可以碰/杠/过':'等待中')}`;document.getElementById('hand').innerHTML=s.hand.map((x,i)=>`<button class="${x.id==s.dragonId?'tile dragon':'tile'}" ${s.canAct?'':'disabled'} onclick="discard(${i})">${x.name}</button>`).join('');renderTable(s);document.getElementById('log').innerHTML=s.log.join('<br>')}
setInterval(tick,1000);tick();
</script>
</main></html>"""


class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        print("%s - %s" % (self.client_address[0], fmt % args))

    def send_text(self, text, content_type="text/html; charset=utf-8"):
        data = text.encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def send_json(self, obj):
        self.send_text(json.dumps(obj, ensure_ascii=False), "application/json; charset=utf-8")

    def do_GET(self):
        parsed = urlparse(self.path)
        if parsed.path == "/":
            room = get_or_create_room()
            self.send_response(302)
            self.send_header("Location", f"/room/{room.room_id}")
            self.end_headers()
            return
        if parsed.path.startswith("/room/"):
            room_id = parsed.path.split("/")[-1].upper()
            get_or_create_room(room_id)
            self.send_text(HTML)
            return
        if parsed.path.startswith("/api/state/"):
            room_id = parsed.path.split("/")[-1].upper()
            q = parse_qs(parsed.query)
            seat = int(q.get("seat", ["-1"])[0])
            token = q.get("token", [""])[0]
            room = get_or_create_room(room_id)
            if not room.auth(seat, token):
                self.send_json({"ok": False})
                return
            state = room.state(seat)
            state["ok"] = True
            self.send_json(state)
            return
        self.send_response(404)
        self.end_headers()

    def do_POST(self):
        parsed = urlparse(self.path)
        parts = parsed.path.strip("/").split("/")
        if len(parts) < 3 or parts[0] != "api":
            self.send_json({"ok": False, "error": "bad api"})
            return
        action, room_id = parts[1], parts[2].upper()
        room = get_or_create_room(room_id)
        length = int(self.headers.get("Content-Length", "0"))
        params = parse_qs(self.rfile.read(length).decode("utf-8"))
        try:
            if action == "join":
                seat, token = room.join(params.get("name", ["好友"])[0], params.get("token", [""])[0])
                self.send_json({"ok": True, "seat": seat, "token": token})
                return
            seat = int(params.get("seat", ["-1"])[0])
            token = params.get("token", [""])[0]
            if not room.auth(seat, token):
                self.send_json({"ok": False, "error": "auth"})
                return
            if action == "discard":
                room.discard(seat, int(params.get("pos", ["-1"])[0]))
            elif action == "hu":
                room.hu(seat)
            elif action == "pong":
                room.claim(seat, 2)
            elif action == "kong":
                room.claim(seat, 3)
            elif action == "pass":
                room.pass_claim(seat)
            self.send_json({"ok": True})
        except Exception as exc:
            self.send_json({"ok": False, "error": str(exc)})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--host", default="0.0.0.0")
    parser.add_argument("--port", type=int, default=int(os.environ.get("PORT", "8000")))
    args = parser.parse_args()
    server = ThreadingHTTPServer((args.host, args.port), Handler)
    print(f"小马识途麻将云服务器版已启动：http://{args.host}:{args.port}")
    server.serve_forever()


if __name__ == "__main__":
    main()

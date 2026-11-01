"""Komment Pilot v2 — userbot + mini app (faqat mini app orqali boshqariladi)."""
import asyncio
import gc
import hashlib
import hmac
import html
import json
import os
import random
import re
import sys
import time
from collections import OrderedDict, deque
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit

import aiohttp
from aiohttp import web
from telethon import TelegramClient, utils
from telethon import events
from telethon.errors import (
    FloodWaitError,
    InviteHashExpiredError,
    InviteHashInvalidError,
    InviteRequestSentError,
    MsgIdInvalidError,
    UserAlreadyParticipantError,
)
from telethon.network import ConnectionTcpAbridged
from telethon.sessions import StringSession
from telethon.tl import types
from telethon.tl.functions import PingRequest
from telethon.tl.functions.channels import GetFullChannelRequest, JoinChannelRequest
from telethon.tl.functions.messages import (
    CheckChatInviteRequest,
    EditMessageRequest,
    GetDiscussionMessageRequest,
    ImportChatInviteRequest,
    SendMessageRequest,
)
from telethon.tl.functions.updates import GetChannelDifferenceRequest

try:
    import uvloop
except ImportError:
    uvloop = None

VERSION = "2.0"

# ================= ENV =================
API_ID = int(os.environ.get("API_ID", 0))
API_HASH = os.environ.get("API_HASH", "")
STRING_SESSION = os.environ.get("STRING_SESSION", "")
BOT_TOKEN = os.environ.get("BOT_TOKEN", "")
OWNER_ID = int(os.environ.get("OWNER_ID", 0))
PORT = int(os.environ.get("PORT", 8080))
DATABASE_URL = os.environ.get("DATABASE_URL", "")
DATA_FILE = os.environ.get("DATA_FILE", "data.json")
TZ = timezone(timedelta(hours=float(os.environ.get("TZ_OFFSET", "5"))))
_ext = os.environ.get("RENDER_EXTERNAL_URL", "").rstrip("/")
WEBAPP_URL = os.environ.get("WEBAPP_URL") or (f"{_ext}/app" if _ext else "")

if not API_ID or not API_HASH or not STRING_SESSION:
    print("XATO: API_ID, API_HASH yoki STRING_SESSION kiritilmagan!")
    sys.exit(1)

_html_path = Path(__file__).with_name("webapp.html")
WEBAPP_HTML = _html_path.read_bytes() if _html_path.exists() else b""
START_TS = time.time()


# ================= HOLAT (xotirada) =================
def default_state():
    return {
        "active": True,
        "delay": 1.0,
        "mode": "navbat",           # navbat | random
        "poll": float(os.environ.get("POLL_INTERVAL", "1.0")),
        "report": "all",            # all | errors | off
        "logch": None,              # {"id","title","username"}
        "channels": {},             # pid -> kanal
        "order": [],                # kanal tartibi
        "days": {},                 # "YYYY-MM-DD" -> {ok, fail, sum, best}
        "speeds": [],               # oxirgi 40 ta tezlik (ms)
    }


def norm_state(d):
    s = default_state()
    s.update({k: v for k, v in (d or {}).items() if k in s})
    s["channels"] = {int(k): v for k, v in (s["channels"] or {}).items()}
    s["order"] = [int(x) for x in s["order"] if int(x) in s["channels"]]
    for pid in s["channels"]:
        if pid not in s["order"]:
            s["order"].append(pid)
    for c in s["channels"].values():
        c.setdefault("edits", [])
        c.setdefault("idx", 0)
        c.setdefault("paused", False)
        c.setdefault("delay", None)
        c.setdefault("mode", None)
        c.setdefault("linked", None)
        c.setdefault("st", {})
        c.setdefault("warns", [])
    return s


S = default_state()
_dirty = False


def mark_dirty():
    global _dirty
    _dirty = True


def dump_state():
    d = dict(S)
    d["channels"] = {str(k): v for k, v in S["channels"].items()}
    return d


# ================= LOGLAR =================
LOGS = deque(maxlen=1500)
PENDING = []
LOG_SEQ = 0


def log(kind, text, ch=None, **d):
    """kind: ok | edit | err | warn | sys"""
    global LOG_SEQ
    LOG_SEQ += 1
    e = {"id": LOG_SEQ, "ts": round(time.time(), 3), "kind": kind,
         "ch": ch, "text": text, "d": d or None}
    LOGS.append(e)
    PENDING.append(e)
    if kind in ("err", "warn", "sys"):
        print(f"[{kind}] {ch or ''} {text}")
    return e


# ================= SAQLASH: Postgres yoki JSON =================
def clean_dsn(url):
    p = urlsplit(url)
    q = [(k, v) for k, v in parse_qsl(p.query) if k not in ("channel_binding",)]
    return urlunsplit((p.scheme, p.netloc, p.path, urlencode(q), p.fragment))


class Store:
    def __init__(self):
        self.pool = None
        self.kind = "json"
        self.ok = True

    async def init(self):
        if not DATABASE_URL:
            return
        import asyncpg
        # min_size=0 — Neon bo'sh paytda "uxlay" oladi (bepul soatlar tejaladi)
        self.pool = await asyncpg.create_pool(
            clean_dsn(DATABASE_URL), min_size=0, max_size=2,
            max_inactive_connection_lifetime=45, command_timeout=30)
        async with self.pool.acquire() as c:
            await c.execute("CREATE TABLE IF NOT EXISTS kp_state (k text PRIMARY KEY, v text NOT NULL)")
            await c.execute(
                "CREATE TABLE IF NOT EXISTS kp_logs (id bigint PRIMARY KEY, ts double precision,"
                " kind text, ch text, text text, d text)")
        self.kind = "postgres"

    async def load(self):
        global LOG_SEQ
        state, logs = None, []
        if self.pool:
            async with self.pool.acquire() as c:
                v = await c.fetchval("SELECT v FROM kp_state WHERE k='main'")
                rows = await c.fetch("SELECT * FROM kp_logs ORDER BY id DESC LIMIT 1500")
            state = json.loads(v) if v else None
            logs = [{"id": r["id"], "ts": r["ts"], "kind": r["kind"], "ch": r["ch"],
                     "text": r["text"], "d": json.loads(r["d"]) if r["d"] else None}
                    for r in reversed(rows)]
        else:
            if os.path.exists(DATA_FILE):
                try:
                    with open(DATA_FILE, encoding="utf-8") as f:
                        raw = json.load(f)
                    state, logs = raw.get("state"), raw.get("logs", [])
                except Exception as e:
                    print("data.json o'qilmadi:", e)
        for e in logs:
            LOGS.append(e)
        LOG_SEQ = max([e["id"] for e in logs] or [0])
        return state

    async def flush(self):
        global _dirty, PENDING
        if not _dirty and not PENDING:
            return
        state_json = json.dumps(dump_state(), ensure_ascii=False)
        batch, PENDING = PENDING, []
        _dirty = False
        try:
            if self.pool:
                async with self.pool.acquire() as c:
                    async with c.transaction():
                        await c.execute(
                            "INSERT INTO kp_state(k,v) VALUES('main',$1) "
                            "ON CONFLICT (k) DO UPDATE SET v=EXCLUDED.v", state_json)
                        if batch:
                            await c.executemany(
                                "INSERT INTO kp_logs(id,ts,kind,ch,text,d) VALUES($1,$2,$3,$4,$5,$6) "
                                "ON CONFLICT (id) DO NOTHING",
                                [(e["id"], e["ts"], e["kind"], e["ch"], e["text"],
                                  json.dumps(e["d"], ensure_ascii=False) if e["d"] else None)
                                 for e in batch])
                            await c.execute(
                                "DELETE FROM kp_logs WHERE id < (SELECT COALESCE(MAX(id),0)-5000 FROM kp_logs)")
            else:
                payload = json.dumps({"state": json.loads(state_json), "logs": list(LOGS)},
                                     ensure_ascii=False)

                def _w():
                    tmp = DATA_FILE + ".tmp"
                    with open(tmp, "w", encoding="utf-8") as f:
                        f.write(payload)
                    os.replace(tmp, DATA_FILE)
                await asyncio.get_running_loop().run_in_executor(None, _w)
            self.ok = True
        except Exception as e:
            self.ok = False
            PENDING = batch + PENDING
            _dirty = True
            print("saqlash xato:", e)


store = Store()


async def saver_loop():
    while True:
        await asyncio.sleep(10)
        await store.flush()


async def save_now():
    mark_dirty()
    await store.flush()


# ================= TELEGRAM =================
client = TelegramClient(
    StringSession(STRING_SESSION), API_ID, API_HASH,
    connection=ConnectionTcpAbridged, connection_retries=None,
    retry_delay=1, auto_reconnect=True, request_retries=2,
    flood_sleep_threshold=0,
)

group_to_channel = {}   # guruh_id -> kanal_id
input_peers = {}
texts = {}              # FAOL kanal_id -> matn (oldindan tayyor)
done = OrderedDict()
seen = OrderedDict()


def _lru_add(od, key, limit=5000):
    if key in od:
        return False
    od[key] = None
    if len(od) > limit:
        od.popitem(last=False)
    return True


def rebuild_texts():
    texts.clear()
    for pid, c in S["channels"].items():
        if not c.get("paused"):
            texts[pid] = c.get("text") or "..."


async def get_peer(pid):
    p = input_peers.get(pid)
    if p is None:
        p = input_peers[pid] = await client.get_input_entity(pid)
    return p


def ch_name(pid):
    c = S["channels"].get(pid) or {}
    return c.get("title") or c.get("username") or str(pid)


def fmt_t(dt):
    return dt.astimezone(TZ).strftime("%H:%M:%S") if dt else "—"


def post_link(pid, post_id, comment_id=None):
    c = S["channels"].get(pid) or {}
    u = c.get("username")
    base = f"https://t.me/{u}/{post_id}" if u else f"https://t.me/c/{str(pid)[4:]}/{post_id}"
    return base + (f"?comment={comment_id}" if comment_id else "")


# ================= ⚡ HOT PATH =================
def _sent_info(result, rid):
    if isinstance(result, types.UpdateShortSentMessage):
        return result.id, result.date
    ups = getattr(result, "updates", []) or []
    mid = None
    for u in ups:
        if isinstance(u, types.UpdateMessageID) and u.random_id == rid:
            mid = u.id
    for u in ups:
        if isinstance(u, (types.UpdateNewChannelMessage, types.UpdateNewMessage)):
            if getattr(u.message, "id", None) == mid:
                return mid, u.message.date
    return mid, None


async def send_comment(ch_id, gpeer, reply_id, post_id, t0, post_date, src, recv_wall):
    if not _lru_add(done, (ch_id, post_id)):
        return
    rid = random.getrandbits(63)
    ts = time.perf_counter()
    try:
        result = await client(SendMessageRequest(
            peer=gpeer, message=texts.get(ch_id, "..."), random_id=rid,
            no_webpage=True,
            reply_to=types.InputReplyToMessage(reply_to_msg_id=reply_id),
        ))
        te = time.perf_counter()
        asyncio.create_task(after_send(ch_id, gpeer, result, rid, post_id, post_date, {
            "total": round((te - t0) * 1000, 1), "wait": round((ts - t0) * 1000, 1),
            "send": round((te - ts) * 1000, 1), "src": src, "recv_wall": recv_wall}))
    except FloodWaitError as e:
        fail(ch_id, post_id, f"FloodWait: {e.seconds} s", post_date)
    except Exception as e:
        fail(ch_id, post_id, f"{type(e).__name__}: {e}"[:200], post_date)


async def on_group_msg(gid, msg):
    fwd = msg.fwd_from
    if not fwd:
        return
    ch_id = group_to_channel[gid]
    if ch_id not in texts:
        return
    post_id = None
    sp = fwd.saved_from_peer
    if sp is not None and utils.get_peer_id(sp) == ch_id:
        post_id = fwd.saved_from_msg_id
    elif msg.from_id is not None and utils.get_peer_id(msg.from_id) == ch_id:
        post_id = fwd.channel_post
    if not post_id or (ch_id, post_id) in done:
        return
    t0 = time.perf_counter()
    try:
        _keep(copy_info, (ch_id, post_id), int((msg.date - (fwd.date or msg.date)).total_seconds()))
    except Exception:
        pass
    await send_comment(ch_id, await get_peer(gid), msg.id, post_id, t0,
                       fwd.date or msg.date, "guruh", time.time())


post_seen = OrderedDict()  # (kanal, post) -> post birinchi ko'rilgan vaqt
disc_info = OrderedDict()  # (kanal, post) -> [so'rovlar soni, nusxa topilgan vaqt]
copy_info = OrderedDict()  # (kanal, post) -> guruhdagi nusxa sanasi - post sanasi (s)


def _keep(d, k, v):
    d[k] = v
    if len(d) > 2000:
        d.popitem(last=False)


def _retry_gap(elapsed):
    # boshida juda tez, keyin siyrakroq (FloodWait bo'lmasligi uchun)
    return 0.25 if elapsed < 6 else 0.5


async def on_channel_msg(ch_id, msg):
    t0 = time.perf_counter()
    recv_wall = time.time()
    post_id = msg.id
    post_seen[(ch_id, post_id)] = recv_wall
    if len(post_seen) > 2000:
        post_seen.popitem(last=False)
    start_burst(ch_id, post_id, msg.date)
    peer = await get_peer(ch_id)
    disc = None
    info = [0, None]
    _keep(disc_info, (ch_id, post_id), info)
    while True:
        if (ch_id, post_id) in done:
            return  # guruh yo'li ulgurdi
        el = time.perf_counter() - t0
        if el > 20:
            break
        try:
            info[0] += 1
            disc = await client(GetDiscussionMessageRequest(peer=peer, msg_id=post_id))
            if disc.messages:
                info[1] = time.time()
                break
        except MsgIdInvalidError:
            pass
        except FloodWaitError as e:
            if e.seconds > 4:
                return  # guruh yo'li (burst poll) davom etadi
            await asyncio.sleep(e.seconds + 0.05)
            continue
        except Exception as e:
            if _lru_add(done, (ch_id, post_id)):
                fail(ch_id, post_id, f"{type(e).__name__}: {e}"[:200], msg.date)
            return
        await asyncio.sleep(_retry_gap(el))
    if not disc or not disc.messages:
        if _lru_add(done, (ch_id, post_id)):
            fail(ch_id, post_id, "20 s ichida muhokama posti paydo bo'lmadi (izohlar yopiq bo'lishi mumkin)", msg.date)
        return
    m = disc.messages[0]
    gid = utils.get_peer_id(m.peer_id)
    if gid not in input_peers:
        for chat in disc.chats:
            if utils.get_peer_id(chat) == gid:
                input_peers[gid] = utils.get_input_peer(chat)
    group_to_channel.setdefault(gid, ch_id)
    await send_comment(ch_id, await get_peer(gid), m.id, post_id, t0, msg.date, "kanal", recv_wall)


async def dispatch(msg):
    if not S["active"] or not isinstance(msg, types.Message):
        return
    pid = utils.get_peer_id(msg.peer_id)
    if pid in group_to_channel:
        if not msg.out and _lru_add(seen, (pid, msg.id)):
            await on_group_msg(pid, msg)
    elif pid in texts:
        if _lru_add(seen, (pid, msg.id)):
            await on_channel_msg(pid, msg)


@client.on(events.Raw(types.UpdateNewChannelMessage))
async def on_raw(update):
    await dispatch(update.message)


# ================= FON: STATISTIKA, TAHRIR, HISOBOT =================
def _today():
    return datetime.now(TZ).strftime("%Y-%m-%d")


def bump_stats(pid, ok, ms=None):
    day = S["days"].setdefault(_today(), {"ok": 0, "fail": 0, "sum": 0.0, "best": None})
    c = S["channels"].get(pid)
    st = c.setdefault("st", {}) if c else {}
    if ok:
        day["ok"] += 1
        day["sum"] += ms
        day["best"] = ms if day["best"] is None else min(day["best"], ms)
        st["ok"] = st.get("ok", 0) + 1
        st["sum"] = st.get("sum", 0) + ms
        st["best"] = ms if st.get("best") is None else min(st["best"], ms)
        S["speeds"] = (S["speeds"] + [ms])[-40:]
    else:
        day["fail"] += 1
        st["fail"] = st.get("fail", 0) + 1
    if len(S["days"]) > 14:
        for k in sorted(S["days"])[:-14]:
            S["days"].pop(k, None)
    mark_dirty()


async def send_report(text, is_error=False):
    lc = S.get("logch")
    if not lc or S["report"] == "off" or (S["report"] == "errors" and not is_error):
        return None
    for attempt in range(2):
        try:
            return await client.send_message(await get_peer(lc["id"]), text,
                                             parse_mode="html", link_preview=False)
        except FloodWaitError as e:
            if attempt:
                break
            await asyncio.sleep(e.seconds + 1)
        except Exception as e:
            log("warn", f"Log kanaliga yuborilmadi: {e}", lc.get("title"))
            break
    return None


def fail(ch_id, post_id, reason, post_date=None):
    bump_stats(ch_id, False)
    c = S["channels"].get(ch_id) or {}
    st = c.setdefault("st", {}) if c else {}
    st.update(last_status="err", last_err=reason, last_at=time.time(), last_post=post_id)
    link = post_link(ch_id, post_id)
    log("err", f"Izoh yozilmadi: {reason}", ch_name(ch_id), post=post_id, link=link,
        post_time=fmt_t(post_date))
    asyncio.create_task(send_report(
        "❌ <b>Izoh yozilmadi</b>\n\n"
        f"📢 <b>{html.escape(ch_name(ch_id))}</b>\n"
        f"🕒 Post: <code>{fmt_t(post_date)}</code>\n"
        f"⚠️ Sabab: <code>{html.escape(reason)}</code>\n"
        f"🔗 <a href=\"{link}\">Postni ochish</a>", True))


def pick_edit(c):
    edits = c.get("edits") or []
    if not edits:
        return None, None
    mode = c.get("mode") or S["mode"]
    if mode == "random":
        i = random.randrange(len(edits))
    else:
        i = c.get("idx", 0) % len(edits)
        c["idx"] = i + 1
    return i, edits[i]


async def after_send(ch_id, gpeer, result, rid, post_id, post_date, tm):
    try:
        cid, cdate = _sent_info(result, rid)
        diff = round((cdate - post_date).total_seconds(), 2) if cdate and post_date else None
        recv = round(tm["recv_wall"] - post_date.timestamp(), 2) if post_date else None
        ps = post_seen.get((ch_id, post_id))
        seen_s = round(ps - post_date.timestamp(), 2) if ps and post_date else None
        bump_stats(ch_id, True, tm["total"])
        c = S["channels"].get(ch_id) or {}
        link = post_link(ch_id, post_id, cid)
        st = c.setdefault("st", {}) if c else {}
        st.update(last_status="ok", last_ms=tm["total"], last_at=time.time(), last_post=post_id,
                  wait=tm["wait"], send=tm["send"], recv=recv, diff=diff, src=tm["src"], last_err=None)
        entry = log("ok", f"Izoh yozildi — {tm['total']:.0f} ms", ch_name(ch_id),
                    ms=tm["total"], wait=tm["wait"], send=tm["send"], recv=recv, diff=diff,
                    src=tm["src"], seen=seen_s, post=post_id, comment=cid, link=link,
                    post_time=fmt_t(post_date), comment_time=fmt_t(cdate))
        src_name = "izoh guruhi" if tm["src"] == "guruh" else "kanal posti"
        extra = ""
        cl = copy_info.get((ch_id, post_id))
        if cl is not None:
            extra += f"🧬 Nusxa sanasi: <code>+{cl} s</code>\n"
        gid_ = next((g for g, c in group_to_channel.items() if c == ch_id), None)
        rs = burst_rtt.get(gid_)
        if rs:
            extra += f"🔁 Poll javobi: <code>o'rtacha {sum(rs) / len(rs):.0f} ms, eng sekin {max(rs):.0f} ms</code>\n"
        di = disc_info.get((ch_id, post_id))
        if di and post_date:
            fnd = (f"{round(di[1] - post_date.timestamp(), 2)} s da topildi" if di[1] else "topilmadi")
            extra += f"🔎 Kanal yo'li: <code>{di[0]} so'rov, {fnd}</code>\n"
        base = (
            "✅ <b>Izoh yozildi</b>\n\n"
            f"📢 <b>{html.escape(ch_name(ch_id))}</b>\n"
            f"🕒 Post: <code>{fmt_t(post_date)}</code>\n"
            f"💬 Izoh: <code>{fmt_t(cdate)}</code>\n"
            f"⚡ Yuborish: <code>{tm['total']:.1f} ms</code>"
            f" (kutish {tm['wait']:.0f} + so'rov {tm['send']:.0f})\n"
            f"📥 Kelishi: <code>{recv if recv is not None else '—'} s</code> · {src_name}\n"
            f"👁 Kanalda ko'rildi: <code>{seen_s if seen_s is not None else '—'} s</code>\n"
            f"{extra}"
            f"⏱ Server farqi: <code>{diff if diff is not None else '—'} s</code>\n"
            f"🔗 <a href=\"{link}\">Izohni ochish</a>"
        )
        report_task = asyncio.create_task(send_report(base))

        idx, edit = pick_edit(c) if c else (None, None)
        if edit is None or not cid:
            return
        delay = c.get("delay")
        delay = S["delay"] if delay is None else delay
        await asyncio.sleep(max(0.0, float(delay)))
        status = None
        for attempt in range(2):
            try:
                await client(EditMessageRequest(peer=gpeer, id=cid, message=edit, no_webpage=True))
                status = f"✏️ Tahrirlandi: <b>{idx + 1}-matn</b> ({delay} s dan keyin)"
                log("edit", f"{idx + 1}-matnga tahrirlandi", ch_name(ch_id),
                    new_text=edit, delay=delay, link=link)
                break
            except FloodWaitError as fw:
                if attempt:
                    status = f"✏️ Tahrir xatosi: FloodWait {fw.seconds} s"
                else:
                    await asyncio.sleep(fw.seconds + 1)
            except Exception as e:
                status = f"✏️ Tahrir xatosi: <code>{html.escape(str(e)[:100])}</code>"
                log("err", f"Tahrir xatosi: {e}", ch_name(ch_id), link=link)
                break
        rep = await report_task
        if rep and status:
            try:
                await rep.edit(base + "\n" + status, parse_mode="html", link_preview=False)
            except Exception:
                pass
    except Exception as e:
        log("err", f"Ichki xato (after_send): {e}", ch_name(ch_id))


# ================= POLLER =================
pollers = {}
_poll_err = {}
pts_state = {}       # guruh/kanal -> oxirgi pts (poll va burst baham ko'radi)
BURST_GAP = 0.1      # burst poll oralig'i (s) — AGRESSIV rejim
BURST_INFLIGHT = 4   # bir vaqtda ochiq turishi mumkin bo'lgan burst so'rovlar soni
burst_rtt = {}       # guruh -> so'nggi burst so'rovlar davomiyligi (ms)
burst_posts = {}     # guruh -> [(kanal, post, tugash vaqti)]
burst_tasks = {}


async def _diff(pid, peer):
    pts = pts_state.get(pid)
    if pts is None:
        pts = (await client(GetFullChannelRequest(peer))).full_chat.pts
    res = await client(GetChannelDifferenceRequest(
        channel=peer, filter=types.ChannelMessagesFilterEmpty(),
        pts=pts, limit=100, force=True))
    if isinstance(res, types.updates.ChannelDifference):
        pts_state[pid] = res.pts
        for m in res.new_messages:
            asyncio.create_task(dispatch(m))
    elif isinstance(res, types.updates.ChannelDifferenceEmpty):
        pts_state[pid] = res.pts
    else:
        pts_state.pop(pid, None)


async def burst_loop(gid):
    """Post ko'rilgach, izoh guruhini juda tez (~0.12 s) tekshiradi — nusxa paydo bo'lishi bilan ushlash uchun."""
    flood = []
    tasks = set()
    gap = BURST_GAP

    async def one(peer):
        # so'rov oldingisi tugashini kutmaydi: server sekin javob bersa ham yangi ma'lumot tez keladi
        t = time.perf_counter()
        try:
            await _diff(gid, peer)
            burst_rtt.setdefault(gid, deque(maxlen=30)).append((time.perf_counter() - t) * 1000)
        except FloodWaitError as e:
            flood.append(e.seconds)
        except Exception:
            pts_state.pop(gid, None)

    try:
        peer = await get_peer(gid)
        while True:
            now = time.time()
            live = [x for x in burst_posts.get(gid, []) if x[2] > now and (x[0], x[1]) not in done]
            burst_posts[gid] = live
            if not live:
                return
            if now < min(x[3] for x in live):
                await asyncio.sleep(min(x[3] for x in live) - now)
                continue
            if flood:
                secs = max(flood)
                flood.clear()
                if secs > 3:
                    log("warn", f"Burst poll FloodWait {secs} s — to'xtatildi", str(gid))
                    return
                # qisqa FloodWait: kutib, oraliqni biroz sekinlashtirib davom etamiz
                gap = min(0.4, gap * 1.5)
                log("warn", f"Burst poll FloodWait {secs} s — oraliq {gap:.2f} s", str(gid))
                await asyncio.sleep(secs + 0.05)
                continue
            tasks = {x for x in tasks if not x.done()}
            if len(tasks) < BURST_INFLIGHT:
                tasks.add(asyncio.create_task(one(peer)))
            await asyncio.sleep(gap)
    except asyncio.CancelledError:
        raise
    except Exception:
        pts_state.pop(gid, None)


def start_burst(ch_id, post_id, post_date):
    if S["poll"] <= 0:
        return
    gid = next((g for g, c in group_to_channel.items() if c == ch_id), None)
    if gid is None:
        return
    tp = post_date.timestamp() if post_date else time.time()
    # nusxa postdan ~3 s keyin chiqadi: 1.5 s dan boshlab 12 s gacha tez tekshiramiz
    burst_posts.setdefault(gid, []).append((ch_id, post_id, tp + 12, tp + 1.5))
    t = burst_tasks.get(gid)
    if t is None or t.done():
        burst_tasks[gid] = asyncio.create_task(burst_loop(gid))


async def poll_peer(pid):
    pts = None
    while True:
        try:
            iv = S["poll"]
            if iv > 0 and pid not in group_to_channel:
                iv = max(iv, 1.0)  # kanal: sekinroq, guruh: eng tez
            _t = time.perf_counter()
            if iv <= 0 or not (pid in group_to_channel or pid in S["channels"]):
                return
            peer = await get_peer(pid)
            await _diff(pid, peer)
            await asyncio.sleep(max(0.0, iv - (time.perf_counter() - _t)))
        except FloodWaitError as e:
            log("warn", f"Poll FloodWait {e.seconds} s — poll sekinlashtiring", str(pid))
            await asyncio.sleep(e.seconds + 1)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            pts_state.pop(pid, None)
            now = time.time()
            if now - _poll_err.get(pid, 0) > 60:
                _poll_err[pid] = now
                log("warn", f"Poll xatosi: {type(e).__name__}: {e}"[:200], ch_name(group_to_channel.get(pid, pid)))
            await asyncio.sleep(3)


def ensure_pollers():
    if S["poll"] <= 0:
        for t in pollers.values():
            t.cancel()
        pollers.clear()
        return
    want = set(group_to_channel) | set(S["channels"])
    for pid in list(pollers):
        if pid not in want:
            pollers.pop(pid).cancel()
    for pid in want:
        if pid not in pollers or pollers[pid].done():
            pollers[pid] = asyncio.create_task(poll_peer(pid))


# ================= HAVOLALAR (ochiq + yopiq) =================
RE_INVITE = re.compile(r"(?:t(?:elegram)?\.me|telegram\.dog)/(?:\+|joinchat/)([\w-]+)", re.I)
RE_CPRIV = re.compile(r"t\.me/c/(\d+)", re.I)
RE_PUBLIC = re.compile(r"(?:t(?:elegram)?\.me|telegram\.dog)/(?:s/)?([A-Za-z][\w]{3,})", re.I)


def parse_link(s):
    s = (s or "").strip()
    if not s:
        raise ValueError("Havola kiriting")
    m = RE_INVITE.search(s)
    if m:
        return "invite", m.group(1)
    if s.startswith("+") and len(s) > 6 and not s[1:].isdigit():
        return "invite", s[1:]
    m = RE_CPRIV.search(s)
    if m:
        return "id", int("-100" + m.group(1))
    if re.fullmatch(r"-?\d{5,}", s):
        n = int(s)
        return "id", n if str(n).startswith("-100") else int("-100" + str(abs(n)))
    m = RE_PUBLIC.search(s)
    if m:
        return "user", m.group(1)
    s2 = s.lstrip("@")
    if re.fullmatch(r"[A-Za-z][\w]{3,}", s2):
        return "user", s2
    raise ValueError("Havola tushunilmadi. Namuna: @kanal, t.me/kanal, t.me/+AbCd...")


async def resolve_link(s):
    """(entity, izoh) qaytaradi. Yopiq havolada kerak bo'lsa a'zo bo'ladi."""
    kind, v = parse_link(s)
    if kind == "invite":
        try:
            info = await client(CheckChatInviteRequest(v))
        except InviteHashExpiredError:
            raise ValueError("Taklif havolasi eskirgan yoki bekor qilingan")
        except InviteHashInvalidError:
            raise ValueError("Taklif havolasi noto'g'ri")
        if isinstance(info, types.ChatInviteAlready):
            return info.chat, None
        try:
            res = await client(ImportChatInviteRequest(v))
            chats = (getattr(res, "chats", None)
                     or getattr(getattr(res, "updates", None), "chats", None) or [])
            chat = next((c for c in chats if isinstance(c, types.Channel)), None)
            if chat is None:  # har qanday Telethon versiyasi uchun
                info = await client(CheckChatInviteRequest(v))
                chat = getattr(info, "chat", None)
            if chat is None:
                raise ValueError("Qo'shildi, lekin kanal ma'lumoti olinmadi — qayta urinib ko'ring")
            return chat, "Havola orqali qo'shildi"
        except UserAlreadyParticipantError:
            info = await client(CheckChatInviteRequest(v))
            return getattr(info, "chat", None), None
        except InviteRequestSentError:
            raise ValueError("Qo'shilish so'rovi yuborildi. Admin tasdiqlagach, havolani qayta kiriting")
    try:
        return await client.get_entity(v), None
    except Exception:
        if kind == "id":
            raise ValueError("Bu yopiq kanalga a'zo emassiz — taklif havolasini (t.me/+...) kiriting")
        raise ValueError("Kanal topilmadi")


async def _join(entity):
    try:
        await client(JoinChannelRequest(entity))
        return None
    except UserAlreadyParticipantError:
        return None
    except InviteRequestSentError:
        return "qo'shilish so'rovi yuborildi, tasdiqlanishi kerak"
    except Exception as e:
        return str(e)[:120]


async def inspect_channel(pid, entity=None):
    """A'zolik, izoh guruhi, yozish huquqini tekshiradi. Ogohlantirishlar ro'yxati."""
    warns = []
    peer = await get_peer(pid)
    full = await client(GetFullChannelRequest(peer))
    me_chan = next((c for c in full.chats if utils.get_peer_id(c) == pid), entity)
    if me_chan is not None and getattr(me_chan, "left", False):
        e = await _join(me_chan)
        if e:
            warns.append(f"Kanalga a'zo bo'lib bo'lmadi: {e}")
    lid = full.full_chat.linked_chat_id
    c = S["channels"].get(pid)
    if not lid:
        warns.append("Izohlar yopiq — kanalga muhokama guruhi ulanmagan")
        if c is not None:
            c["linked"] = None
        return warns
    gid = int(f"-100{lid}")
    chat = next((x for x in full.chats if x.id == lid), None)
    if chat is not None:
        input_peers[gid] = utils.get_input_peer(chat)
        if getattr(chat, "left", False):
            e = await _join(chat)
            if e:
                warns.append(f"Izoh guruhiga a'zo bo'lib bo'lmadi: {e}")
        dbr = getattr(chat, "default_banned_rights", None)
        if dbr is not None and dbr.send_messages:
            warns.append("Izoh guruhida yozish taqiqlangan")
        if getattr(chat, "join_request", False):
            warns.append("Izoh guruhi qo'shilish so'rovini talab qiladi")
    group_to_channel[gid] = pid
    if c is not None:
        c["linked"] = {"id": gid, "title": getattr(chat, "title", "")}
    return warns


# ================= AMALLAR (mini app) =================
def need(pid):
    c = S["channels"].get(pid)
    if not c:
        raise ValueError("Kanal topilmadi")
    return c


async def op_add_channel(link, text):
    text = (text or "").strip()
    if not text:
        raise ValueError("Izoh matnini kiriting")
    entity, note = await resolve_link(link)
    if not (isinstance(entity, types.Channel) and entity.broadcast):
        raise ValueError("Bu kanal emas (guruh yoki foydalanuvchi)")
    pid = utils.get_peer_id(entity)
    input_peers[pid] = utils.get_input_peer(entity)
    c = S["channels"].get(pid)
    if c:
        c.update(text=text, title=entity.title, username=entity.username)
    else:
        S["channels"][pid] = c = {
            "id": pid, "title": entity.title, "username": entity.username,
            "invite": link.strip() if "+" in link or "joinchat" in link else None,
            "text": text, "edits": [], "idx": 0, "paused": False,
            "delay": None, "mode": None, "linked": None, "st": {}, "warns": [],
            "added": time.time(),
        }
        S["order"].append(pid)
    warns = await inspect_channel(pid, entity)
    c["warns"] = warns
    if note:
        warns = [note] + warns
    rebuild_texts()
    ensure_pollers()
    log("sys", "Kanal qo'shildi" + (f" ({'; '.join(warns)})" if warns else ""), entity.title)
    await save_now()
    return pid, warns


async def op_update_channel(pid, b):
    c = need(pid)
    changed = []
    if "text" in b:
        t = (b["text"] or "").strip()
        if not t:
            raise ValueError("Izoh matni bo'sh bo'lmasin")
        c["text"] = t
        changed.append("matn")
    if "paused" in b:
        c["paused"] = bool(b["paused"])
        changed.append("pauza" if c["paused"] else "faol")
    if "delay" in b:
        c["delay"] = None if b["delay"] in (None, "") else max(0.0, min(3600.0, float(b["delay"])))
        changed.append("kutish")
    if "mode" in b:
        c["mode"] = b["mode"] if b["mode"] in ("navbat", "random") else None
        changed.append("usul")
    rebuild_texts()
    log("sys", "Kanal yangilandi: " + ", ".join(changed), ch_name(pid))
    await save_now()


async def op_del_channel(pid):
    c = S["channels"].pop(pid, None)
    if pid in S["order"]:
        S["order"].remove(pid)
    for gid, ch in list(group_to_channel.items()):
        if ch == pid:
            group_to_channel.pop(gid, None)
    rebuild_texts()
    ensure_pollers()
    if c:
        log("sys", "Kanal o'chirildi", c.get("title"))
    await save_now()


async def op_check_channel(pid):
    c = need(pid)
    warns = await inspect_channel(pid)
    c["warns"] = warns
    rebuild_texts()
    ensure_pollers()
    log("warn" if warns else "sys",
        "Tekshiruv: " + ("; ".join(warns) if warns else "hammasi joyida ✅"), ch_name(pid))
    await save_now()
    return warns


async def op_add_edit(pid, text):
    c = need(pid)
    t = (text or "").strip()
    if not t:
        raise ValueError("Tahrir matni bo'sh")
    c["edits"].append(t)
    log("sys", f"{len(c['edits'])}-tahrir matni qo'shildi", ch_name(pid))
    await save_now()


async def op_del_edit(pid, idx):
    c = need(pid)
    if 0 <= idx < len(c["edits"]):
        c["edits"].pop(idx)
        log("sys", f"{idx + 1}-tahrir matni o'chirildi", ch_name(pid))
        await save_now()


async def op_settings(b):
    changed = []
    if "active" in b:
        S["active"] = bool(b["active"])
        changed.append("avto-izoh " + ("yoqildi" if S["active"] else "o'chirildi"))
    if "delay" in b:
        S["delay"] = round(max(0.0, min(3600.0, float(b["delay"]))), 2)
        changed.append(f"kutish {S['delay']} s")
    if "mode" in b and b["mode"] in ("navbat", "random"):
        S["mode"] = b["mode"]
        changed.append(f"usul {S['mode']}")
    if "report" in b and b["report"] in ("all", "errors", "off"):
        S["report"] = b["report"]
        changed.append(f"hisobot {S['report']}")
    if "poll" in b:
        v = float(b["poll"])
        S["poll"] = 0.0 if v <= 0 else round(max(0.1, min(5.0, v)), 2)
        ensure_pollers()
        changed.append(f"poll {S['poll'] or 'o`chiq'}")
    if changed:
        log("sys", "Sozlama: " + ", ".join(changed))
    await save_now()


async def op_set_logch(link):
    entity, note = await resolve_link(link)
    if not isinstance(entity, types.Channel):
        raise ValueError("Log uchun kanal kerak")
    if not (entity.creator or (entity.admin_rights and (entity.admin_rights.post_messages or not entity.broadcast))):
        raise ValueError("Bu kanalga yozish huquqi yo'q — userbot akkauntini admin qiling")
    pid = utils.get_peer_id(entity)
    input_peers[pid] = utils.get_input_peer(entity)
    S["logch"] = {"id": pid, "title": entity.title, "username": entity.username}
    log("sys", "Log kanali ulandi" + (f" ({note})" if note else ""), entity.title)
    await save_now()


async def op_test_logch():
    if not S.get("logch"):
        raise ValueError("Log kanali ulanmagan")
    m = await client.send_message(await get_peer(S["logch"]["id"]),
                                  "🧪 <b>Komment Pilot</b> — test xabari. Log kanali ishlayapti ✅",
                                  parse_mode="html")
    if not m:
        raise ValueError("Yuborilmadi")
    log("sys", "Log kanaliga test yuborildi", S["logch"]["title"])


async def op_ping():
    res = []
    for _ in range(3):
        s = time.perf_counter()
        await client(PingRequest(ping_id=random.getrandbits(63)))
        res.append((time.perf_counter() - s) * 1000)
    return round(min(res), 1), round(sum(res) / len(res), 1)


def snapshot():
    day = S["days"].get(_today(), {"ok": 0, "fail": 0, "sum": 0, "best": None})
    chans = []
    for pid in S["order"]:
        c = S["channels"].get(pid)
        if not c:
            continue
        st = c.get("st", {})
        n = len(c["edits"])
        chans.append({
            "id": str(pid), "title": c.get("title"), "username": c.get("username"),
            "text": c.get("text"), "edits": c["edits"], "paused": c.get("paused", False),
            "delay": c.get("delay"), "mode": c.get("mode"),
            "linked": c.get("linked"), "warns": c.get("warns", []),
            "next": (c.get("idx", 0) % n) + 1 if n else None,
            "st": {k: st.get(k) for k in ("ok", "fail", "best", "last_ms", "last_at", "last_status",
                                          "last_err", "wait", "send", "recv", "diff", "src")}
                  | {"avg": round(st["sum"] / st["ok"], 1) if st.get("ok") else None},
        })
    return {
        "v": VERSION, "active": S["active"], "delay": S["delay"], "mode": S["mode"],
        "poll": S["poll"], "report": S["report"], "logch": S["logch"],
        "today": {"ok": day["ok"], "fail": day["fail"], "best": day["best"],
                  "avg": round(day["sum"] / day["ok"], 1) if day["ok"] else None},
        "speeds": S["speeds"], "channels": chans,
        "recent": list(LOGS)[-6:][::-1],
        "sys": {"dc": client.session.dc_id, "uptime": int(time.time() - START_TS),
                "db": store.kind, "db_ok": store.ok, "connected": client.is_connected()},
    }


# ================= MINI APP API =================
def check_init_data(init_data):
    if not BOT_TOKEN or not OWNER_ID or not init_data:
        return False
    try:
        pairs = dict(parse_qsl(init_data, keep_blank_values=True))
        h = pairs.pop("hash", "")
        dcs = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
        secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
        if not hmac.compare_digest(hmac.new(secret, dcs.encode(), hashlib.sha256).hexdigest(), h):
            return False
        if time.time() - int(pairs.get("auth_date", 0)) > 86400 * 7:
            return False
        return json.loads(pairs.get("user", "{}")).get("id") == OWNER_ID
    except Exception:
        return False


@web.middleware
async def mw(request, handler):
    if request.path.startswith("/api/"):
        if not check_init_data(request.headers.get("X-Init-Data", "")):
            return web.json_response({"error": "Ruxsat yo'q"}, status=403)
        try:
            return await handler(request)
        except (ValueError, KeyError, TypeError) as e:
            return web.json_response({"error": str(e) or "Noto'g'ri so'rov"}, status=400)
        except FloodWaitError as e:
            return web.json_response({"error": f"Telegram cheklovi: {e.seconds} s kuting"}, status=429)
        except Exception as e:
            log("err", f"API xato {request.path}: {e}")
            return web.json_response({"error": f"{type(e).__name__}: {e}"[:200]}, status=500)
    return await handler(request)


async def body(r):
    try:
        return await r.json()
    except Exception:
        return {}


def ok(**extra):
    d = snapshot()
    d.update(extra)
    return web.json_response(d)


async def a_state(r):
    return ok()


async def a_logs(r):
    kind = r.query.get("kind", "")
    q = r.query.get("q", "").lower()
    before = int(r.query.get("before", 0) or 0)
    out = []
    for e in reversed(LOGS):
        if before and e["id"] >= before:
            continue
        if kind and e["kind"] != kind and not (kind == "err" and e["kind"] == "warn"):
            continue
        if q and q not in (e["text"] or "").lower() and q not in (e["ch"] or "").lower():
            continue
        out.append(e)
        if len(out) >= 60:
            break
    return web.json_response({"logs": out})


async def a_settings(r):
    await op_settings(await body(r))
    return ok()


async def a_ch_add(r):
    b = await body(r)
    pid, warns = await op_add_channel(b.get("link", ""), b.get("text", ""))
    return ok(added=str(pid), warn=warns)


async def a_ch_update(r):
    b = await body(r)
    await op_update_channel(int(b["id"]), b)
    return ok()


async def a_ch_del(r):
    await op_del_channel(int((await body(r))["id"]))
    return ok()


async def a_ch_check(r):
    warns = await op_check_channel(int((await body(r))["id"]))
    return ok(warn=warns, checked=True)


async def a_edit_add(r):
    b = await body(r)
    await op_add_edit(int(b["id"]), b.get("text", ""))
    return ok()


async def a_edit_del(r):
    b = await body(r)
    await op_del_edit(int(b["id"]), int(b["index"]))
    return ok()


async def a_logch(r):
    b = await body(r)
    act = b.get("action")
    if act == "set":
        await op_set_logch(b.get("link", ""))
    elif act == "del":
        S["logch"] = None
        log("sys", "Log kanali uzildi")
        await save_now()
    elif act == "test":
        await op_test_logch()
    return ok()


async def a_ping(r):
    mn, avg = await op_ping()
    return ok(ping={"min": mn, "avg": avg})


async def h_root(r):
    return web.Response(text="Komment Pilot ishlayapti")


async def h_app(r):
    if not WEBAPP_HTML:
        return web.Response(text="webapp.html topilmadi", status=404)
    return web.Response(body=WEBAPP_HTML, content_type="text/html", charset="utf-8",
                        headers={"Cache-Control": "no-cache"})


async def start_web():
    app = web.Application(middlewares=[mw])
    app.router.add_get("/", h_root)
    app.router.add_get("/app", h_app)
    app.router.add_get("/api/state", a_state)
    app.router.add_get("/api/logs", a_logs)
    app.router.add_get("/api/ping", a_ping)
    app.router.add_post("/api/settings", a_settings)
    app.router.add_post("/api/channel/add", a_ch_add)
    app.router.add_post("/api/channel/update", a_ch_update)
    app.router.add_post("/api/channel/del", a_ch_del)
    app.router.add_post("/api/channel/check", a_ch_check)
    app.router.add_post("/api/edit/add", a_edit_add)
    app.router.add_post("/api/edit/del", a_edit_del)
    app.router.add_post("/api/logch", a_logch)
    runner = web.AppRunner(app, access_log=None)
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", PORT).start()


# ================= BOT (faqat panelni ochish uchun) =================
async def bot_loop():
    if not BOT_TOKEN:
        return
    base = f"https://api.telegram.org/bot{BOT_TOKEN}/"
    async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=70)) as s:
        try:
            await s.post(base + "deleteWebhook")
            if WEBAPP_URL:
                await s.post(base + "setChatMenuButton", json={"menu_button": {
                    "type": "web_app", "text": "Panel", "web_app": {"url": WEBAPP_URL}}})
        except Exception as e:
            log("warn", f"Bot sozlanmadi: {e}")
        offset = 0
        while True:
            try:
                async with s.get(base + "getUpdates", params={
                        "timeout": 50, "offset": offset, "allowed_updates": '["message"]'}) as r:
                    data = await r.json()
                for u in data.get("result", []):
                    offset = u["update_id"] + 1
                    uid = ((u.get("message") or {}).get("from") or {}).get("id")
                    if not uid:
                        continue
                    if uid != OWNER_ID:
                        await s.post(base + "sendMessage", json={"chat_id": uid, "text": "⛔ Bu bot shaxsiy."})
                        continue
                    p = {"chat_id": uid, "parse_mode": "HTML",
                         "text": "⚡ <b>Komment Pilot</b>\n\nHammasi panel orqali boshqariladi 👇"}
                    if WEBAPP_URL:
                        p["reply_markup"] = {"inline_keyboard": [[{
                            "text": "🎛 Panelni ochish", "web_app": {"url": WEBAPP_URL}}]]}
                    await s.post(base + "sendMessage", json=p)
            except asyncio.CancelledError:
                raise
            except Exception:
                await asyncio.sleep(5)


# ================= ISHGA TUSHIRISH =================
async def warmup():
    await client.get_dialogs()
    for pid in list(S["channels"]):
        try:
            await get_peer(pid)
            c = S["channels"][pid]
            c["warns"] = await inspect_channel(pid)
        except Exception as e:
            S["channels"][pid]["warns"] = [f"Tekshirib bo'lmadi: {e}"]
            log("warn", f"Ishga tushishda tekshirib bo'lmadi: {e}", ch_name(pid))
    if S.get("logch"):
        try:
            await get_peer(S["logch"]["id"])
        except Exception as e:
            log("warn", f"Log kanali topilmadi: {e}")
    rebuild_texts()
    ensure_pollers()


async def main():
    global S
    await start_web()
    try:
        await store.init()
    except Exception as e:
        print("Postgres ulanmadi, JSON ishlatiladi:", e)
        store.pool, store.kind = None, "json"
    S = norm_state(await store.load())
    await client.start()
    me = await client.get_me()
    await warmup()
    log("sys", f"Ishga tushdi: {me.first_name} · DC{client.session.dc_id} · {store.kind} · "
               f"{len(texts)} faol kanal")
    await save_now()
    asyncio.create_task(saver_loop())
    asyncio.create_task(bot_loop())
    gc.collect()
    gc.freeze()
    print(">>> Komment Pilot v2 ishga tushdi!")
    await client.run_until_disconnected()


if __name__ == "__main__":
    if uvloop:
        uvloop.run(main())
    else:
        asyncio.run(main())

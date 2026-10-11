#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import asyncio
import calendar
import html as htmlmod
import urllib.parse
import csv
import json
import re as regex
import urllib.request
import time
import os
import mimetypes
import signal
import sqlite3
import threading
from collections import deque
from urllib.parse import unquote, urlsplit, parse_qs
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from math import radians, sin, cos, atan2, degrees, sqrt, asin, acos

MAIN_LOOP = None

# =========================
# Config
# =========================
# Don't edit these defaults: copy my_settings.example.py to my_settings.py and put your own
# values there (home location, IPs, Pushover keys...). Anything in my_settings.py overrides
# the defaults here, and updating this file never touches it.
ACARSHUB_HOST = "127.0.0.1"   # host running acars_router
ACARS_PORT    = 15550         # acars_router TCP serve port for ACARS (JSON lines)
VDLM2_PORT    = 15555         # acars_router TCP serve port for VDLM2 (JSON lines)
TAR1090_URL   = "http://127.0.0.1:8080/data/aircraft.json"   # tar1090 / ultrafeeder aircraft.json

HTTP_PORT     = 8000
WS_PORT       = 8765

# Home coordinates (for distance calc & map center) -- set these in my_settings.py
HOME_LAT = 0.0
HOME_LON = 0.0

# Base & state paths
BASE_DIR   = os.path.dirname(os.path.abspath(__file__))
STATE_PATH = os.path.join(BASE_DIR, "state.json")
ALERTS_PATH= os.path.join(BASE_DIR, "alerts.txt")

# Persisted history files
STORED_HISTORY_PATH = os.path.join(BASE_DIR, "messages_recent.json")

ALERTS_HISTORY_PATH = os.path.join(BASE_DIR, "message_alerts.json")
MAX_ALERT_HISTORY   = 200

# Long-term message log (SQLite) for the Trends tab
DB_PATH            = os.path.join(BASE_DIR, "message_log.db")
DB_RETENTION_DAYS  = 90      # rows older than this are pruned
DB_FLUSH_SEC       = 60      # batch writes to spare the SD card

# ACARS-reported positions (POS reports, ADS-C) shown on the map
ACARS_POS_MAX_AGE  = 1800    # seconds a reported position stays on the map
ACARS_POS_MAX_MI   = 1000    # ignore positions further than this (bad decodes)

# Flight routes
ROUTE_LOOKUP_ENABLED = True  # set False to never contact adsbdb.com (routes from messages still work)
ROUTE_API_URL      = "https://api.adsbdb.com/v0/callsign/{}"
ROUTE_CACHE_PATH   = os.path.join(BASE_DIR, "route_cache.json")
ROUTE_CACHE_DAYS   = 2       # how long a looked-up route is kept before asking adsbdb again
ROUTE_MISS_HOURS   = 24      # how long to remember "no route known" before asking again
ROUTE_LOOKUP_GAP   = 1.5     # seconds between lookups (be polite to the free API)
RADIO_ROUTE_HOURS  = 14      # how long a route reported by the aircraft itself is kept
# Charter / fractional operators fly different trips every day, so a stored route for their
# flight numbers is meaningless. Never look these up.
ROUTE_SKIP_OPERATORS = {"EJA", "NJE", "LXJ", "EJM", "VJT", "XSR", "JTL", "KFS"}
# Route sanity check: a route is only shown if the aircraft's position fits it
ROUTE_FIT_NEAR_MI    = 40     # within this of origin/destination, always accept (departure/arrival paths)
ROUTE_FIT_XTRACK_MI  = 60     # max distance off the origin->destination line ...
ROUTE_FIT_XTRACK_PCT = 0.15   # ... or this fraction of the route length, whichever is larger
ROUTE_FIT_HEADING    = 80     # max degrees between track and bearing to destination (when > 80 mi out)
AIRPORTS_CSV_URL   = "https://davidmegginson.github.io/ourairports-data/airports.csv"
AIRPORTS_PATH      = os.path.join(BASE_DIR, "airports.csv")

# Flown-path trails (built from ADS-B positions)
TRAIL_MIN_SEC      = 8       # minimum seconds between trail points
TRAIL_MAX_POINTS   = 900     # per aircraft (~2 hours at the minimum spacing)
TRAIL_KEEP_SEC     = 900     # keep a trail this long after the aircraft drops off ADS-B

# Local weather (METAR) shown in the page header
METAR_STATION      = ""      # ICAO code of your nearest airport with a METAR, e.g. "KMCI"; blank = off
METAR_URL          = "https://aviationweather.gov/api/data/metar?ids={}&format=json"
METAR_POLL_SEC     = 300     # aviationweather.gov asks for no more than 1 request/minute

# Pushover notifications for alert messages (keywords in alerts.txt).
# Get both keys at https://pushover.net. Leave either blank to turn notifications off.
PUSHOVER_TOKEN        = ""   # Pushover application API token
PUSHOVER_USER         = ""   # Pushover user key (or a group key)
PUSHOVER_PRIORITY     = 0    # -1 quiet, 0 normal, 1 high (ignores your quiet hours)
PUSHOVER_SOUND        = ""   # e.g. "pushover", "siren", "cosmic"; blank = your default sound
PUSHOVER_DEDUP_MIN    = 10   # don't repeat the same flight + text within this many minutes
PUSHOVER_MAX_PER_HOUR = 30   # safety cap in case a keyword turns out to be very common

# Emergency squawks (7500 / 7600 / 7700 and the ADS-B emergency flag)
PUSHOVER_EMERGENCY_PRIORITY = 1        # 1 = high (ignores quiet hours); 2 = repeats until you acknowledge
PUSHOVER_EMERGENCY_SOUND    = "siren"  # blank = your default sound

# Nightly station summary sent to Pushover
SUMMARY_ENABLED            = True
SUMMARY_TIME               = "21:00"   # local time, 24-hour clock; covers midnight up to this time
PUSHOVER_SUMMARY_PRIORITY  = 0

# Coverage map (farthest ACARS / VDLM2 contact in each direction)
COVERAGE_BIN_DEG   = 5        # one outline point per 5 degrees of bearing
COVERAGE_MAX_MI    = 350      # ignore anything farther (VHF can't reach that far; bad decode)

# Flight timeline
FLIGHT_LOG_HOURS   = 24      # how long a flight's messages are kept for the timeline (memory only)

# Takeoff / landing detector (watch airports for rapid climbs and descents nearby)
# Add your local airport(s) in my_settings.py, e.g.
#   AIRPORT_WATCH = [{"code": "MCI", "name": "Kansas City Intl", "lat": 39.2976, "lon": -94.7139, "elev": 1026}]
AIRPORT_WATCH = []
AP_RADIUS_MI       = 5.0     # only aircraft this close to the airport
AP_MAX_AGL         = 2500    # ...and below this height above the field (ft)
AP_CLIMB_FPM       = 500     # climbing at least this fast  -> departure
AP_DESCENT_FPM     = -400    # descending at least this fast -> arrival
AP_BADGE_SEC       = 900     # how long the DEP / ARR badge stays on a flight

# Background timing
ADSB_POLL_SEC    = 2       # how often the server polls tar1090
STATUS_PUSH_SEC  = 5       # how often status is pushed to browsers
HISTORY_SAVE_SEC = 30      # how often message history is flushed to disk

# Server start time
SERVER_START_TIME = time.time()

# =========================
# State (persisted)
# =========================
total_message_count   = 0
frequency_counts      = {}                 # str MHz -> int
airline_counts        = {}                 # airline name -> int
distance_bins         = [0, 0, 0, 0, 0]    # 0–25, 25–50, 50–100, 100–200, 200+
matched_message_count = 0                  # messages with verified location

# Non-persisted runtime state
MAX_MESSAGES    = 200
stored_messages = []                       # recent messages to seed UI on connect
alerts_history  = []                       # persisted: last 200 'Message Alert' messages
history_dirty   = False
message_seq     = 0
stream_status   = {"acars": False, "vdlm2": False, "adsb": False}
adsb_aircraft   = {}                       # hex -> {data, last_seen}; replaced atomically by the poller
adsb_snapshot   = b'{"aircraft": [], "now": 0}'
ADSB_TIMEOUT    = 30

# Message rates (per 60s window)
RATE_WINDOW_SEC = 60
acars_times = deque()
vdlm2_times = deque()
adsb_last_sum = None
adsb_last_t   = None
adsb_rate     = 0.0

# Recently verified aircraft (by hex) for map highlighting
RECENT_VERIFY_WINDOW = 120  # seconds
recent_verified = {}        # hex -> last_verified_timestamp

# Positions reported over ACARS/VDLM2 (key -> latest report)
acars_positions = {}

# Rows waiting to be written to the SQLite log
db_buffer = []

# Alerts (keywords from alerts.txt, case-insensitive whole words)
alert_terms = []
alert_patterns = []
alert_terms_mtime = 0

# =========================
# Plane Watch (config + state)
# =========================
WATCHLIST_PATH       = os.path.join(BASE_DIR, "plane_alerts.txt")  # same dir as alerts.txt
watchlist_tokens     = []      # lowercase tokens from file
watch_token_info     = {}      # token -> {'owner': str, 'tail': str}
watchlist_mtime      = 0
WATCH_NEAR_MI        = 75      # only show tracked pill if <= this radius
WATCH_MIN_TOKEN_LEN  = 3       # ignore overly-short tokens to avoid false positives

# =========================
# Persistence helpers
# =========================
def _atomic_write_json(path, obj):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(obj, f)
    os.replace(tmp, path)

def save_state():
    try:
        state = {
            "version": 3,
            "total_message_count": total_message_count,
            "airline_counts": airline_counts,
            "frequency_counts": frequency_counts,
            "distance_bins": distance_bins,
            "matched_message_count": matched_message_count,
        }
        _atomic_write_json(STATE_PATH, state)
        print(f"[STATE] Saved -> {STATE_PATH}")
    except Exception as e:
        print(f"[STATE] Save failed: {e}")

def load_state():
    global total_message_count, airline_counts, frequency_counts, distance_bins, matched_message_count
    try:
        if os.path.isfile(STATE_PATH):
            with open(STATE_PATH, "r") as f:
                state = json.load(f)
            total_message_count     = int(state.get("total_message_count", 0))
            airline_counts.update(state.get("airline_counts", {}))
            frequency_counts.update(state.get("frequency_counts", {}))
            bins = state.get("distance_bins")
            if isinstance(bins, list) and len(bins) == 5:
                for i in range(5):
                    distance_bins[i] = int(bins[i])
            matched_message_count = int(state.get("matched_message_count", 0))
            print(f"[STATE] Loaded <- {STATE_PATH}")
        else:
            print(f"[STATE] No existing state file, starting fresh")
    except Exception as e:
        print(f"[STATE] Load failed: {e}")

async def periodic_state_save():
    while True:
        await asyncio.sleep(60)
        save_state()

def _on_shutdown(sig, frame=None):
    print(f"[STATE] Caught {sig}, saving state…")
    try:
        save_state()
        save_stored_history()
        save_alerts_history()
        db_write(db_buffer[:])
        save_route_cache()
        save_coverage()
    finally:
        os._exit(0)


# -------------------------
# Message history (persisted last 200) + alert history
# -------------------------
def load_stored_history():
    """Load last 200 general messages (all, not just alerts) from disk into stored_messages."""
    global stored_messages
    try:
        if os.path.isfile(STORED_HISTORY_PATH):
            with open(STORED_HISTORY_PATH, "r", encoding="utf-8", errors="ignore") as f:
                arr = json.load(f) or []
            stored_messages = arr[-MAX_MESSAGES:] if isinstance(arr, list) else []
        else:
            stored_messages = []
    except Exception as e:
        print(f"[MSG-HIST] Load failed: {e}")
        stored_messages = []

def save_stored_history():
    """Persist stored_messages to disk (max MAX_MESSAGES)."""
    global history_dirty
    try:
        _atomic_write_json(STORED_HISTORY_PATH, (stored_messages or [])[-MAX_MESSAGES:])
        history_dirty = False
    except Exception as e:
        print(f"[MSG-HIST] Save failed: {e}")

async def periodic_history_save():
    # Flush message history periodically instead of on every message (saves SD card writes).
    while True:
        await asyncio.sleep(HISTORY_SAVE_SEC)
        if history_dirty:
            save_stored_history()

def load_alerts_history():
    """Load persisted 'Message Alert' history from disk into alerts_history (max MAX_ALERT_HISTORY)."""
    global alerts_history
    try:
        if os.path.isfile(ALERTS_HISTORY_PATH):
            with open(ALERTS_HISTORY_PATH, "r", encoding="utf-8", errors="ignore") as f:
                arr = json.load(f) or []
            alerts_history = [a for a in arr if isinstance(a, dict)] if isinstance(arr, list) else []
        else:
            alerts_history = []
    except Exception as e:
        print(f"[ALERTS-HIST] Load failed: {e}")
        alerts_history = []
    # Older files have no alert IDs: give each a stable one so it can be starred.
    for i, a in enumerate(alerts_history):
        if not a.get("aid"):
            a["aid"] = f"{int(float(a.get('timestamp') or 0) * 1000)}-old{i}"
        a["starred"] = bool(a.get("starred"))
    trim_alerts()

def trim_alerts():
    """Keep every starred alert plus the newest MAX_ALERT_HISTORY unstarred ones."""
    unstarred = [a for a in alerts_history if not a.get("starred")]
    if len(unstarred) > MAX_ALERT_HISTORY:
        drop = {id(a) for a in unstarred[:len(unstarred) - MAX_ALERT_HISTORY]}
        alerts_history[:] = [a for a in alerts_history if id(a) not in drop]

def star_alert(aid, starred) -> bool:
    for a in alerts_history:
        if a.get("aid") == aid:
            a["starred"] = bool(starred)
            save_alerts_history()
            return True
    return False

def reset_alerts() -> int:
    """Delete every alert that isn't starred. Returns how many were removed."""
    before = len(alerts_history)
    alerts_history[:] = [a for a in alerts_history if a.get("starred")]
    save_alerts_history()
    removed = before - len(alerts_history)
    print(f"[ALERTS-HIST] Reset: removed {removed}, kept {len(alerts_history)} starred")
    return removed

def save_alerts_history():
    """Persist alerts_history to disk (max MAX_ALERT_HISTORY)."""
    try:
        _atomic_write_json(ALERTS_HISTORY_PATH, alerts_history or [])
    except Exception as e:
        print(f"[ALERTS-HIST] Save failed: {e}")

# =========================
# Alerts loader
# =========================
def load_alert_terms():
    """Load alert keywords (case-insensitive) from alerts.txt; one per line. Blank/# lines ignored."""
    global alert_terms, alert_patterns, alert_terms_mtime
    try:
        if not os.path.isfile(ALERTS_PATH):
            if alert_terms:
                print("[ALERTS] alerts.txt removed; alerts disabled")
            alert_terms = []
            alert_patterns = []
            alert_terms_mtime = 0
            return
        m = os.path.getmtime(ALERTS_PATH)
        if m == alert_terms_mtime:
            return
        terms = []
        with open(ALERTS_PATH, "r", encoding="utf-8", errors="ignore") as f:
            for line in f:
                s = line.strip()
                if not s or s.startswith("#"):
                    continue
                terms.append(s.lower())
        # Compiled whole-word patterns (case-insensitive)
        patterns = []
        for t in terms:
            esc = regex.escape(t)
            patterns.append(regex.compile(rf'(?<![A-Za-z0-9_]){esc}(?![A-Za-z0-9_])', flags=regex.IGNORECASE))
        alert_terms = terms
        alert_patterns = patterns
        alert_terms_mtime = m
        print(f"[ALERTS] Loaded {len(alert_terms)} terms from alerts.txt")
    except Exception as e:
        print(f"[ALERTS] Load failed: {e}")

def save_alert_terms(terms) -> list:
    """Write a new keyword list to alerts.txt (keeping its leading # comment lines) and reload it."""
    global alert_terms_mtime
    clean, seen = [], set()
    for t in terms or []:
        s = " ".join(str(t).replace("\r", " ").replace("\n", " ").split()).lower()[:100]
        if s and not s.startswith("#") and s not in seen:
            seen.add(s)
            clean.append(s)
    clean = clean[:200]
    header = []
    try:
        if os.path.isfile(ALERTS_PATH):
            with open(ALERTS_PATH, "r", encoding="utf-8", errors="ignore") as f:
                for line in f:
                    if line.strip().startswith("#"):
                        header.append(line.rstrip("\n"))
                    elif line.strip():
                        break
    except Exception:
        pass
    if not header:
        header = ["# Alert keywords: one word or phrase per line (whole-word, not case sensitive).",
                  "# Edited from the dashboard's Alerts tab."]
    tmp = ALERTS_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write("\n".join(header + clean) + "\n")
    os.replace(tmp, ALERTS_PATH)
    alert_terms_mtime = 0          # force a reload even if the clock hasn't ticked
    load_alert_terms()
    print(f"[ALERTS] Keywords saved from dashboard ({len(alert_terms)} terms)")
    return alert_terms

async def periodic_alert_reload():
    while True:
        try:
            load_alert_terms()
        except Exception as e:
            print(f"[ALERTS] Reload error: {e}")
        await asyncio.sleep(60)

def is_alert_message(txt: str) -> bool:
    if not txt:
        return False
    for pat in alert_patterns:
        try:
            if pat.search(txt):
                return True
        except Exception:
            continue
    return False

# =========================
# Plane watch list loader
# =========================
def load_watchlist():
    """Load watch tokens from plane_alerts.txt. CSV preferred: hex,tail,owner,planeType. Header/comments (#) allowed."""
    global watchlist_tokens, watchlist_mtime, watch_token_info
    try:
        if not os.path.isfile(WATCHLIST_PATH):
            watchlist_tokens = []; watch_token_info = {}; watchlist_mtime = 0
            return
        mtime = os.path.getmtime(WATCHLIST_PATH)
        if mtime == watchlist_mtime:
            return
        toks = []; info = {}
        with open(WATCHLIST_PATH, "r", encoding="utf-8", errors="ignore") as f:
            for raw in f:
                s = raw.strip()
                if not s or s.startswith("#"): continue
                parts = [p.strip() for p in s.split(",")]
                if len(parts) >= 3:
                    hexv = (parts[0] or "").strip()
                    tail = (parts[1] or "").strip()
                    owner= (parts[2] or "").strip()
                    for token in [hexv.lower(), tail.lower()]:
                        if token and len(token) >= WATCH_MIN_TOKEN_LEN:
                            toks.append(token); info[token] = {"owner": owner, "tail": tail}
                else:
                    for token in regex.split(r"[\s,]+", s):
                        token = token.strip().lower()
                        if token and len(token) >= WATCH_MIN_TOKEN_LEN:
                            toks.append(token); info[token] = {"owner": "", "tail": ""}
        watchlist_tokens = toks; watch_token_info = info; watchlist_mtime = mtime
        print(f"[WATCH] Loaded {len(watchlist_tokens)} tokens from plane_alerts.txt")
    except Exception as e:
        print(f"[WATCH] Load failed: {e}")

async def periodic_watch_reload():
    while True:
        try:
            load_watchlist()
        except Exception as e:
            print(f"[WATCH] Reload error: {e}")
        await asyncio.sleep(60)

def compute_watch_list():
    """Return a sorted list (nearest first) of all watch matches within WATCH_NEAR_MI, fresh by ADSB_TIMEOUT."""
    out = []
    aircraft_map = adsb_aircraft
    if not watchlist_tokens or not aircraft_map:
        return out
    now = time.time()
    for hex_id, info in aircraft_map.items():
        last = info.get("last_seen") or 0
        if (now - last) > ADSB_TIMEOUT:
            continue
        ac = info.get("data") or {}
        lat = ac.get("lat"); lon = ac.get("lon")
        if not isinstance(lat, (int,float)) or not isinstance(lon, (int,float)):
            continue
        flight = str(ac.get("flight") or "").strip().upper()
        reg    = str(ac.get("r") or ac.get("reg") or "").strip().upper()
        hexv   = str(ac.get("hex") or hex_id or "").strip().upper()

        fields_lc = [flight.lower(), reg.lower(), hexv.lower()]
        matched_token = None
        for t in watchlist_tokens:
            if any(t in f for f in fields_lc):
                matched_token = t; break
        if not matched_token:
            continue

        d = calculate_distance_miles(HOME_LAT, HOME_LON, float(lat), float(lon))
        if not (d == d) or d > WATCH_NEAR_MI:
            continue

        brg = bearing_deg(HOME_LAT, HOME_LON, float(lat), float(lon))
        owner = watch_token_info.get(matched_token, {}).get("owner", "")
        tail_file = watch_token_info.get(matched_token, {}).get("tail", "")
        tail_show = (tail_file or reg or "").upper()
        out.append({
            "hex": hexv, "flight": flight, "reg": reg, "tail": tail_show, "owner": owner,
            "distance": round(float(d), 1), "cardinal": bearing_to_cardinal(brg),
            "lat": float(lat), "lon": float(lon)
        })
    out.sort(key=lambda x: x.get("distance", 9e9))
    return out

# =========================
# Helpers for VDLM2 text extraction
# =========================
def _collect_strings(obj):
    """Depth-first: collect all short-ish strings inside obj."""
    out = []
    def walk(x):
        if x is None:
            return
        if isinstance(x, str):
            s = x.strip()
            if s and len(s) <= 2000:
                out.append(s)
        elif isinstance(x, dict):
            for v in x.values():
                walk(v)
        elif isinstance(x, (list, tuple)):
            for v in x:
                walk(v)
    walk(obj)
    return out

def _coalesce_unique(parts, sep=" | "):
    """Join unique non-empty parts in order."""
    seen = set()
    uniq = []
    for p in parts:
        s = (p or "").strip()
        if not s or s in seen:
            continue
        seen.add(s)
        uniq.append(s)
    return sep.join(uniq)

# =========================
# ACARS POS… position-report parser
# =========================
def _decode_deg_tenths_minutes(val: str, is_lat: bool) -> float | None:
    """
    Convert ddmmm (lat) / dddmmm (lon) where mmm = tenths of minutes into decimal degrees.
    Example: 36569 -> 36° 56.9' -> 36.9483…
             094584 -> 94° 58.4' -> 94.9733…
    """
    try:
        if is_lat:
            if not (len(val) == 5 and val.isdigit()): return None
            deg = int(val[:2]); tmin = int(val[2:])
        else:
            if not (len(val) == 6 and val.isdigit()): return None
            deg = int(val[:3]); tmin = int(val[3:])
        minutes = tmin / 10.0
        return deg + (minutes / 60.0)
    except Exception:
        return None

def parse_acars_posn(text: str) -> dict | None:
    """
    Parse lines like:
      POSN36569W094584,ZAL-24,202133,380,FSM-25,202812,KLAWW,M50,28556,4219BF4

    Returns dict with keys:
      pos_lat, pos_lon, parsed_alt_ft, parsed_route, parsed_oat_c, parsed_checksum, parsed_summary
    """
    if not text: return None
    t = text.strip().upper()

    m = regex.search(r'POS([NS])(\d{5})([EW])(\d{6})', t)
    if not m:
        return None

    hemi_lat, lat_raw, hemi_lon, lon_raw = m.groups()
    lat = _decode_deg_tenths_minutes(lat_raw, is_lat=True)
    lon = _decode_deg_tenths_minutes(lon_raw, is_lat=False)
    if lat is None or lon is None:
        return None
    if hemi_lat == 'S': lat = -lat
    if hemi_lon == 'W': lon = -lon

    parts = t.split(',')
    pos_idx = next((i for i,p in enumerate(parts) if 'POS' in p), -1)
    tail = parts[pos_idx+1:] if pos_idx >= 0 else parts

    wpt1, time1, alt_hund, wpt2, time2, wpt3, oat, *_rest = (tail + [None]*8)[:8]

    alt_ft = None
    if alt_hund and alt_hund.isdigit():
        alt_ft = int(alt_hund) * 100

    def fmt_time(s):
        if isinstance(s, str) and len(s) == 6 and s.isdigit():
            return f"{s[0:2]}:{s[2:4]}:{s[4:6]}"
        return None
    t1 = fmt_time(time1)
    t2 = fmt_time(time2)

    oat_c = None
    if isinstance(oat, str) and regex.fullmatch(r'[MP]\d{1,2}', oat):
        sign = -1 if oat.startswith('M') else 1
        oat_c = sign * int(oat[1:])

    chk = None
    if tail:
        last = tail[-1]
        if isinstance(last, str):
            m2 = regex.search(r'([0-9A-F]{4})$', last)
            if m2:
                chk = "0x" + m2.group(1).lower()

    segs = []
    if wpt1:
        segs.append(f"{wpt1}@{t1}" if t1 else f"{wpt1}")
    if wpt2:
        segs.append(f"{wpt2}@{t2}" if t2 else f"{wpt2}")
    if wpt3:
        segs.append(wpt3)
    route = " > ".join(segs) if segs else None

    summary = f"Position Report: {abs(lat):.3f}° {'S' if lat<0 else 'N'}, {abs(lon):.3f}° {'W' if lon<0 else 'E'}"
    if alt_ft is not None:
        summary += f" • Alt {alt_ft} ft"
    if route:
        summary += f" • Route {route}"
    if oat_c is not None:
        summary += f" • OAT {oat_c}°C"

    return {
        "pos_lat": round(lat, 6),
        "pos_lon": round(lon, 6),
        "parsed_alt_ft": alt_ft,
        "parsed_route": route,
        "parsed_oat_c": oat_c,
        "parsed_checksum": chk,
        "parsed_summary": summary
    }

# =========================
# Ground Station Squitter parser
# =========================
GS_SQUITTER_RE = regex.compile(
    r'(?P<ver>\d{2})(?P<type>[A-Z])A(?P<iata>[A-Z]{3})(?P<icao>[A-Z]{4})'
    r'(?P<site>\d{1,2})'
    r'(?P<latdeg>\d{2})(?P<latmin>\d{2})(?P<lathemi>[NS])'
    r'(?P<londeg>\d{3})(?P<lonmin>\d{2})(?P<lonhemi>[EW])'
    r'(?P<band>[A-Z])(?P<freq>\d{6})\s*/\s*(?P<network>[A-Z]+)'
)

def parse_ground_station_squitter(s: str) -> dict | None:
    if not isinstance(s, str):
        return None
    m = GS_SQUITTER_RE.search(s.strip().upper())
    if not m:
        return None

    g = m.groupdict()

    # Interpret ddmm as dd.mm to match requested output
    lat = int(g["latdeg"]) + int(g["latmin"]) / 100.0
    if g["lathemi"] == "S":
        lat = -lat
    lon = int(g["londeg"]) + int(g["lonmin"]) / 100.0
    if g["lonhemi"] == "W":
        lon = -lon

    freq_mhz = int(g["freq"]) / 1000.0

    return {
        "parsed_description": "Ground Station Squitter",
        "parsed_network": g["network"],
        "parsed_version": int(g["ver"]),
        "parsed_ground_station": f"{g['icao']}{g['site']}",
        "parsed_iata": g["iata"],
        "parsed_icao": g["icao"],
        "parsed_gs_lat": round(lat, 4),
        "parsed_gs_lon": round(lon, 4),
        "parsed_vdl_freq_mhz": round(freq_mhz, 3),
        "parsed_summary": (
            f"GS Squitter • {g['network']} v{g['ver']} • {g['icao']}{g['site']} "
            f"({g['iata']}/{g['icao']}) @ {lat:.2f}, {lon:.2f} • {freq_mhz:.3f} MHz"
        ),
    }

# =========================
# Airline parser (main US carriers)
# =========================
AIRLINE_CODES = {
    "AA": "American Airlines", "AAL": "American Airlines",
    "UA": "United Airlines",   "UAL": "United Airlines",
    "DL": "Delta Air Lines",   "DAL": "Delta Air Lines",
    "WN": "Southwest Airlines","SWA": "Southwest Airlines",
    "AS": "Alaska Airlines",   "ASA": "Alaska Airlines",
    "B6": "JetBlue Airways",   "JBU": "JetBlue Airways",
    "F9": "Frontier Airlines", "FFT": "Frontier Airlines",
    "NK": "Spirit Airlines",   "NKS": "Spirit Airlines",
    "OO": "SkyWest Airlines",  "SKW": "SkyWest Airlines",
    "MQ": "Envoy Air",         "ENY": "Envoy Air",
    "FX": "FedEx Express",     "FDX": "FedEx Express",
    "5X": "UPS Airlines",      "UPS": "UPS Airlines",
}

def parse_airline(flight):
    if not flight:
        return None
    f = str(flight).strip().upper()
    code2 = f[:2]
    if code2 in AIRLINE_CODES: return AIRLINE_CODES[code2]
    code3 = f[:3]
    if code3 in AIRLINE_CODES: return AIRLINE_CODES[code3]
    return None

def _split_flight(f: str):
    """'AAL123' / 'AA0123' -> ('AAL', 123, '') ; returns None if not airline-style."""
    m = regex.match(r'^([A-Z]{3}|[A-Z0-9]{2})(\d{1,4})([A-Z]?)$', f)
    if not m:
        return None
    return m.group(1), int(m.group(2)), m.group(3)

def flights_match(a, b) -> bool:
    """
    True when two flight IDs refer to the same flight. Handles IATA vs ICAO forms
    (AA0123 == AAL123) for known airlines; otherwise requires an exact match.
    """
    a = regex.sub(r'[^A-Z0-9]', '', str(a or "").upper())
    b = regex.sub(r'[^A-Z0-9]', '', str(b or "").upper())
    if not a or not b:
        return False
    if a == b:
        return True
    pa, pb = _split_flight(a), _split_flight(b)
    if not pa or not pb:
        return False
    air_a, air_b = parse_airline(pa[0]), parse_airline(pb[0])
    return bool(air_a) and air_a == air_b and pa[1] == pb[1] and pa[2] == pb[2]

def _norm_reg(s: str) -> str:
    return regex.sub(r'[^A-Z0-9]', '', str(s or "").upper())

# =========================
# Helpers (distance, uptime, rates, bearing)
# =========================
def calculate_distance_miles(lat1, lon1, lat2, lon2):
    R = 3958.8
    lat1, lon1, lat2, lon2 = map(radians, [lat1, lon1, lat2, lon2])
    dlat = lat2 - lat1; dlon = lon2 - lon1
    A = sin(dlat/2)**2 + cos(lat1)*cos(lat2)*sin(dlon/2)**2
    return R * 2 * atan2(sqrt(A), sqrt(1-A))

def get_distance_bin_index(miles):
    if miles <= 25: return 0
    if miles <= 50: return 1
    if miles <= 100: return 2
    if miles <= 200: return 3
    return 4

def format_uptime():
    uptime_seconds = int(time.time() - SERVER_START_TIME)
    days = uptime_seconds // 86400
    hours = (uptime_seconds % 86400) // 3600
    minutes = (uptime_seconds % 3600) // 60
    return f"{days}d {hours}h {minutes}m"

def _prune_times(q: deque, now: float):
    cutoff = now - RATE_WINDOW_SEC
    while q and q[0] < cutoff:
        q.popleft()

def get_rates_now():
    now = time.time()
    _prune_times(acars_times, now)
    _prune_times(vdlm2_times, now)
    acars_rate = len(acars_times) / RATE_WINDOW_SEC
    vdlm2_rate = len(vdlm2_times) / RATE_WINDOW_SEC
    total_rate = acars_rate + vdlm2_rate
    return acars_rate, vdlm2_rate, total_rate, adsb_rate

def bearing_deg(lat1, lon1, lat2, lon2):
    """Initial bearing in degrees from (lat1, lon1) to (lat2, lon2)."""
    lat1r, lat2r = radians(lat1), radians(lat2)
    dlon = radians(lon2 - lon1)
    x = sin(dlon) * cos(lat2r)
    y = cos(lat1r) * sin(lat2r) - sin(lat1r) * cos(lat2r) * cos(dlon)
    return (degrees(atan2(x, y)) + 360.0) % 360.0

def bearing_to_cardinal(b):
    """Convert bearing degrees to 16-wind compass (N, NNE, NE, ...)."""
    dirs = ["N","NNE","NE","ENE","E","ESE","SE","SSE",
            "S","SSW","SW","WSW","W","WNW","NW","NNW"]
    idx = int((b + 11.25) // 22.5) % 16
    return dirs[idx]

# =========================
# Routes: airports, route sources, trails
# =========================
airports = {}          # ICAO -> {"icao","iata","name","city","lat","lon"}
airports_iata = {}     # IATA -> ICAO
airports_ready = False

radio_routes = {}      # "H:hex" / "T:tail" / "F:flight" -> route reported by the aircraft
route_cache = {}       # callsign -> {"ts": float, "route": dict | None}
route_cache_dirty = False
route_queue = deque()
route_pending = set()

trails = {}            # hex -> {"pts": deque([lat, lon, alt, ts]), "last": ts}

ICAO_FOR_AIRLINE = {}  # airline name -> 3-letter ICAO code (built from AIRLINE_CODES)
for _code, _name in AIRLINE_CODES.items():
    if len(_code) == 3 and _code.isalpha():
        ICAO_FOR_AIRLINE[_name] = _code

def canon_flight(f) -> str:
    """'AA0123' / 'AAL123' -> 'AAL123' for known airlines; otherwise the cleaned ID with leading zeros dropped."""
    f = regex.sub(r'[^A-Z0-9]', '', str(f or "").upper())
    if not f:
        return ""
    p = _split_flight(f)
    if not p:
        return f
    pre, numb, suf = p
    icao = ICAO_FOR_AIRLINE.get(parse_airline(pre) or "", None)
    return f"{icao or pre}{numb}{suf}"

def lookup_callsign(flight) -> str | None:
    """Callsign to send to adsbdb (ICAO airline style only, e.g. AAL123), or None."""
    c = canon_flight(flight)
    if not regex.match(r'^[A-Z]{3}\d{1,4}[A-Z]{0,2}$', c) or c[:3] in ROUTE_SKIP_OPERATORS:
        return None
    return c

def _load_airports_csv():
    global airports_ready
    tmp = AIRPORTS_PATH + ".part"
    try:
        if not os.path.isfile(AIRPORTS_PATH):
            print("[ROUTES] Downloading airport list (one time)…")
            req = urllib.request.Request(AIRPORTS_CSV_URL, headers={"User-Agent": "live-aviation-dashboard"})
            with urllib.request.urlopen(req, timeout=60) as resp, open(tmp, "wb") as fh:
                while True:
                    chunk = resp.read(65536)
                    if not chunk:
                        break
                    fh.write(chunk)
            os.replace(tmp, AIRPORTS_PATH)
        n = 0
        with open(AIRPORTS_PATH, newline="", encoding="utf-8") as fh:
            for row in csv.DictReader(fh):
                typ = row.get("type") or ""
                iata = (row.get("iata_code") or "").strip().upper()
                if typ not in ("large_airport", "medium_airport") and not (typ == "small_airport" and iata):
                    continue
                code = ""
                for k in ("icao_code", "gps_code", "ident"):
                    v = (row.get(k) or "").strip().upper()
                    if regex.match(r'^[A-Z]{4}$', v):
                        code = v
                        break
                if not code:
                    continue
                try:
                    lat, lon = float(row["latitude_deg"]), float(row["longitude_deg"])
                except (KeyError, TypeError, ValueError):
                    continue
                airports.setdefault(code, {
                    "icao": code, "iata": iata or None, "name": row.get("name") or code,
                    "city": row.get("municipality") or None, "lat": lat, "lon": lon,
                })
                if iata:
                    airports_iata.setdefault(iata, code)
                n += 1
        airports_ready = True
        print(f"[ROUTES] Airport list loaded ({n} airports)")
    except Exception as e:
        print(f"[ROUTES] Airport list unavailable ({e}); routes will show as codes without map lines until it loads")
        try:
            os.remove(tmp)
        except OSError:
            pass

def airport_info(code):
    code = str(code or "").strip().upper()
    if not code:
        return None
    if len(code) == 3 and code in airports_iata:
        code = airports_iata[code]
    a = airports.get(code)
    return dict(a) if a else {"icao": code, "iata": None, "name": None, "city": None, "lat": None, "lon": None}

def load_route_cache():
    global route_cache
    try:
        if os.path.exists(ROUTE_CACHE_PATH):
            with open(ROUTE_CACHE_PATH, "r") as f:
                data = json.load(f)
            now = time.time()
            route_cache = {k: v for k, v in data.items()
                           if isinstance(v, dict) and now - v.get("ts", 0) < ROUTE_CACHE_DAYS * 86400}
            # Re-learn airport coordinates that came with cached routes.
            for v in route_cache.values():
                r = v.get("route") or {}
                for a in (r.get("orig_info"), r.get("dest_info")):
                    if isinstance(a, dict) and a.get("icao") and a.get("lat") is not None:
                        airports.setdefault(a["icao"], a)
                        if a.get("iata"):
                            airports_iata.setdefault(a["iata"], a["icao"])
            print(f"[ROUTES] Loaded {len(route_cache)} cached routes")
    except Exception as e:
        print(f"[ROUTES] Could not load route cache: {e}")

def save_route_cache():
    global route_cache_dirty
    if not route_cache_dirty:
        return
    try:
        _atomic_write_json(ROUTE_CACHE_PATH, dict(route_cache))
        route_cache_dirty = False
    except Exception as e:
        print(f"[ROUTES] Could not save route cache: {e}")

async def periodic_route_cache_save():
    while True:
        await asyncio.sleep(300)
        save_route_cache()

def request_route(callsign):
    """Queue an adsbdb lookup for this callsign if we don't already know its route."""
    if not ROUTE_LOOKUP_ENABLED or not callsign:
        return
    c = route_cache.get(callsign)
    if c:
        ttl = ROUTE_CACHE_DAYS * 86400 if c.get("route") else c.get("ttl", ROUTE_MISS_HOURS * 3600)
        if time.time() - c.get("ts", 0) < ttl:
            return
    if callsign in route_pending or len(route_queue) > 500:
        return
    route_pending.add(callsign)
    route_queue.append(callsign)

def _airport_from_api(a):
    if not isinstance(a, dict):
        return None
    icao = str(a.get("icao_code") or "").upper() or None
    if not icao:
        return None
    info = {
        "icao": icao, "iata": (str(a.get("iata_code") or "").upper() or None),
        "name": a.get("name"), "city": a.get("municipality"),
        "lat": a.get("latitude"), "lon": a.get("longitude"),
    }
    if info["lat"] is not None and icao not in airports:
        airports[icao] = info
        if info["iata"]:
            airports_iata.setdefault(info["iata"], icao)
    return info

def route_lookup_loop():
    """Background thread: look up queued callsigns on adsbdb.com, one at a time."""
    global route_cache_dirty
    backoff_until = 0
    while True:
        if not route_queue or time.time() < backoff_until:
            time.sleep(1)
            continue
        cs = route_queue.popleft()
        entry = None
        try:
            req = urllib.request.Request(ROUTE_API_URL.format(cs), headers={
                "User-Agent": "live-aviation-dashboard (hobby ACARS/ADS-B station)",
                "Accept": "application/json",
            })
            with urllib.request.urlopen(req, timeout=8) as resp:
                j = json.loads(resp.read())
            fr = ((j or {}).get("response") or {}).get("flightroute") if isinstance((j or {}).get("response"), dict) else None
            o = _airport_from_api((fr or {}).get("origin"))
            d = _airport_from_api((fr or {}).get("destination"))
            if o and d:
                entry = {"ts": time.time(), "route": {
                    "orig": o["icao"], "dest": d["icao"], "orig_info": o, "dest_info": d,
                    "src": "db", "callsign": cs,
                }}
            else:
                entry = {"ts": time.time(), "route": None}
        except urllib.error.HTTPError as e:
            if e.code == 404:
                entry = {"ts": time.time(), "route": None}
            elif e.code == 429:
                print("[ROUTES] adsbdb rate limit hit; pausing lookups for 2 minutes")
                backoff_until = time.time() + 120
                route_queue.appendleft(cs)
                continue
            else:
                entry = {"ts": time.time(), "route": None, "ttl": 900}
        except Exception:
            # Network trouble: remember briefly so we don't hammer, then retry later.
            entry = {"ts": time.time(), "route": None, "ttl": 900}
        route_cache[cs] = entry
        route_cache_dirty = True
        route_pending.discard(cs)
        time.sleep(ROUTE_LOOKUP_GAP)

def extract_radio_route(data: dict):
    """Pull origin/destination out of the aircraft's own message (OOOI reports, flight plans)."""
    label = str(data.get("label") or "").strip()
    up = str(data.get("msg_text") or "").strip().upper()
    if not up:
        return None
    orig = dest = None
    kind = None
    if label.startswith("Q") and label != "Q0":
        m = AIRPORT_PAIR_RE.match(up)
        if m and m.group(2):
            orig, dest, kind = m.group(1), m.group(2), data.get("msg_type") or "OOOI report"
    if not orig and "FPN/" in up:
        dep = regex.search(r'DA:([A-Z]{4})', up)
        arr = regex.search(r'AA:([A-Z]{4})', up)
        if dep and arr:
            orig, dest, kind = dep.group(1), arr.group(1), "Flight plan"
    if not orig or orig == dest:
        return None
    # When the airport list is loaded, ignore codes that aren't real airports (bad decodes).
    if airports_ready and (orig not in airports or dest not in airports):
        return None
    return {"orig": orig, "dest": dest, "src": "radio", "kind": kind}

def remember_radio_route(route: dict, data: dict):
    now = time.time()
    route = dict(route, ts=now, flight=canon_flight(data.get("flight")) or None)
    keys = []
    for h in (data.get("matched_hex"), data.get("hex")):
        if h:
            keys.append("H:" + str(h).lower())
    t = _norm_reg(data.get("tail"))
    if len(t) >= 3:
        keys.append("T:" + t)
    if route["flight"]:
        keys.append("F:" + route["flight"])
    for k in keys:
        radio_routes[k] = route
    # prune old
    if len(radio_routes) > 3000:
        for k in [k for k, r in radio_routes.items() if now - r["ts"] > RADIO_ROUTE_HOURS * 3600]:
            radio_routes.pop(k, None)

EARTH_MI = 3958.8

def _gc(lat1, lon1, lat2, lon2):
    """(distance miles, initial bearing radians) between two points."""
    p1, p2, dl = radians(lat1), radians(lat2), radians(lon2 - lon1)
    a = sin((p2 - p1) / 2) ** 2 + cos(p1) * cos(p2) * sin(dl / 2) ** 2
    d = 2 * EARTH_MI * atan2(sqrt(a), sqrt(max(0.0, 1 - a)))
    b = atan2(sin(dl) * cos(p2), cos(p1) * sin(p2) - sin(p1) * cos(p2) * cos(dl))
    return d, b

def route_fits(r: dict, pos) -> bool | None:
    """
    Does the aircraft's position (lat, lon, track) fit this route?
    True / False, or None when it can't be judged (missing airport coordinates).
    """
    try:
        olat, olon, dlat, dlon = r.get("o_lat"), r.get("o_lon"), r.get("d_lat"), r.get("d_lon")
        if None in (olat, olon, dlat, dlon):
            return None
        lat, lon, track = pos
        L, b_od = _gc(olat, olon, dlat, dlon)
        d_op, b_op = _gc(olat, olon, lat, lon)
        d_pd, b_pd = _gc(lat, lon, dlat, dlon)
        if d_op <= ROUTE_FIT_NEAR_MI or d_pd <= ROUTE_FIT_NEAR_MI:
            return True
        # cross-track (distance off the great-circle line) and along-track position
        xt = abs(EARTH_MI * asin(max(-1.0, min(1.0, sin(d_op / EARTH_MI) * sin(b_op - b_od)))))
        if xt > max(ROUTE_FIT_XTRACK_MI, ROUTE_FIT_XTRACK_PCT * L):
            return False
        at = EARTH_MI * acos(max(-1.0, min(1.0, cos(d_op / EARTH_MI) / max(1e-9, cos(xt / EARTH_MI)))))
        if cos(b_op - b_od) < 0:
            at = -at
        if at < -ROUTE_FIT_NEAR_MI or at > L + ROUTE_FIT_NEAR_MI:
            return False
        if isinstance(track, (int, float)) and d_pd > 80:
            diff = abs((track - degrees(b_pd) + 540) % 360 - 180)
            if diff > ROUTE_FIT_HEADING:
                return False
        return True
    except Exception:
        return None

def pos_of(ac) -> tuple | None:
    """(lat, lon, track) for an ADS-B aircraft dict, or None."""
    if not ac:
        return None
    lat, lon = ac.get("lat"), ac.get("lon")
    if not isinstance(lat, (int, float)) or not isinstance(lon, (int, float)):
        return None
    trk = ac.get("track")
    if not isinstance(trk, (int, float)):
        trk = ac.get("true_heading") if isinstance(ac.get("true_heading"), (int, float)) else None
    if ac.get("alt_baro") == "ground":
        trk = None   # taxiing headings say nothing about the route
    return (float(lat), float(lon), trk)

def get_route(hex_id=None, tail=None, flight=None, callsign=None, pos=None, why=None):
    """
    Best known route for an aircraft: its own radio report first, then the adsbdb schedule.
    If `pos` (lat, lon, track) is given, routes that don't fit the aircraft's position are rejected;
    a rejected route is described in `why["rejected"]` when a dict is passed.
    """
    def ok(pub):
        if pos is None:
            return True
        if route_fits(pub, pos) is False:
            if why is not None and "rejected" not in why:
                why["rejected"] = f"{pub.get('o_iata') or pub['orig']} → {pub.get('d_iata') or pub['dest']}"
                why["rejected_src"] = pub.get("src")
            return False
        return True

    now = time.time()
    cur = canon_flight(callsign or flight)
    keys = []
    if hex_id:
        keys.append("H:" + str(hex_id).lower())
    t = _norm_reg(tail)
    if len(t) >= 3:
        keys.append("T:" + t)
    if cur:
        keys.append("F:" + cur)
    for k in keys:
        r = radio_routes.get(k)
        if not r or now - r["ts"] > RADIO_ROUTE_HOURS * 3600:
            continue
        # Same aircraft can fly several legs a day: only trust a hex/tail match for the same flight,
        # or (if we don't know the current flight) when the report is recent.
        if k[0] in "HT":
            if cur and r.get("flight") and r["flight"] != cur:
                continue
            # A report with no flight number can't be tied to a leg: only trust it briefly.
            if (not cur or not r.get("flight")) and now - r["ts"] > 2 * 3600:
                continue
        pub = route_public(r)
        if ok(pub):
            return pub
    for cs in (lookup_callsign(callsign), lookup_callsign(flight)):
        if not cs:
            continue
        c = route_cache.get(cs)
        if c and c.get("route"):
            pub = route_public(c["route"])
            if ok(pub):
                return pub
        else:
            request_route(cs)
        break
    return None

def route_public(r: dict) -> dict:
    o = r.get("orig_info") or airport_info(r["orig"])
    d = r.get("dest_info") or airport_info(r["dest"])
    return {
        "orig": r["orig"], "dest": r["dest"],
        "o_iata": o.get("iata"), "d_iata": d.get("iata"),
        "o_name": o.get("name"), "d_name": d.get("name"),
        "o_city": o.get("city"), "d_city": d.get("city"),
        "o_lat": o.get("lat"), "o_lon": o.get("lon"),
        "d_lat": d.get("lat"), "d_lon": d.get("lon"),
        "src": r.get("src", "db"), "kind": r.get("kind"), "ts": r.get("ts"),
    }

def update_trails(active, now):
    for ac in active:
        lat, lon = ac.get("lat"), ac.get("lon")
        if not isinstance(lat, (int, float)) or not isinstance(lon, (int, float)):
            continue
        h = str(ac.get("hex") or "").lower()
        t = trails.get(h)
        if t is None:
            t = trails[h] = {"pts": deque(maxlen=TRAIL_MAX_POINTS), "last": now}
        alt = ac.get("alt_baro")
        alt = alt if isinstance(alt, (int, float)) else (0 if alt == "ground" else None)
        pts = t["pts"]
        if pts:
            plat, plon, _, pts_t = pts[-1]
            if now - pts_t < TRAIL_MIN_SEC and abs(plat - lat) + abs(plon - lon) < 0.02:
                t["last"] = now
                continue
            # A big jump usually means a different flight or a bad position: start fresh.
            if calculate_distance_miles(plat, plon, lat, lon) > 60 and now - pts_t < 120:
                pts.clear()
        pts.append((round(lat, 5), round(lon, 5), alt, now))
        t["last"] = now
    for h in [h for h, t in trails.items() if now - t["last"] > TRAIL_KEEP_SEC]:
        trails.pop(h, None)

def track_payload(hex_id=None, key=None) -> dict:
    hex_id = str(hex_id or "").lower() or None
    out = {"hex": hex_id, "key": key, "trail": [], "route": None, "pos": None}
    if hex_id:
        t = trails.get(hex_id)
        if t:
            out["trail"] = [[p[0], p[1], p[2]] for p in list(t["pts"])]
        info = adsb_aircraft.get(hex_id)
        ac = info["data"] if info else {}
        if ac.get("lat") is not None:
            out["pos"] = [ac["lat"], ac["lon"]]
        out["route"] = get_route(hex_id, ac.get("r") or ac.get("reg"), None, ac.get("flight"), pos=pos_of(ac))
    elif key:
        p = acars_positions.get(key)
        if p:
            out["pos"] = [p["lat"], p["lon"]]
            out["route"] = get_route(p.get("hex"), p.get("tail"), p.get("flight"), pos=(p["lat"], p["lon"], None))
    return out

def trails_payload() -> bytes:
    out = {}
    for h, t in list(trails.items()):
        pts = list(t["pts"])[-200:]
        if len(pts) >= 2:
            out[h] = [[p[0], p[1]] for p in pts]
    return json.dumps({"trails": out}).encode()

# =========================
# Local weather (METAR)
# =========================
metar_latest = None
metar_error = None

def _parse_metar(m: dict) -> dict:
    raw = str(m.get("rawOb") or "")
    inhg = None
    a = regex.search(r'\bA(\d{4})\b', raw)
    if a:
        inhg = int(a.group(1)) / 100.0
    else:
        alt = m.get("altim")
        if isinstance(alt, (int, float)):
            inhg = round(alt * 0.0295300, 2) if alt > 200 else float(alt)
    clouds = []
    for c in m.get("clouds") or []:
        if isinstance(c, dict) and c.get("cover"):
            clouds.append({"cover": c.get("cover"), "base": c.get("base")})
    return {
        "station": m.get("icaoId"), "name": m.get("name"), "obs": m.get("obsTime"),
        "type": m.get("metarType"), "cat": m.get("fltCat") or None,
        "temp": m.get("temp"), "dewp": m.get("dewp"),
        "wdir": m.get("wdir"), "wspd": m.get("wspd"), "wgst": m.get("wgst"),
        "visib": m.get("visib"), "inhg": inhg, "wx": m.get("wxString"),
        "clouds": clouds, "vertvis": m.get("vertVis"), "raw": raw,
    }

def metar_loop():
    global metar_latest, metar_error
    if not METAR_STATION:
        return
    was_ok = None
    while True:
        try:
            req = urllib.request.Request(METAR_URL.format(METAR_STATION), headers={
                "User-Agent": "live-aviation-dashboard (hobby ACARS/ADS-B station)", "Accept": "application/json"})
            with urllib.request.urlopen(req, timeout=15) as resp:
                body = resp.read()
            data = json.loads(body) if body else []
            if isinstance(data, list) and data and isinstance(data[0], dict):
                metar_latest = dict(_parse_metar(data[0]), fetched=time.time())
                metar_error = None
                if was_ok is not True:
                    print(f"[METAR] {METAR_STATION}: {metar_latest['raw']}")
                was_ok = True
            else:
                metar_error = "no recent report"
        except Exception as e:
            metar_error = str(e)
            if was_ok is not False:
                print(f"[METAR] fetch failed: {e}")
            was_ok = False
        time.sleep(METAR_POLL_SEC)

# =========================
# Pushover notifications
# =========================
pushover_queue = deque()
pushover_recent = {}          # (who, text) -> last sent time, for de-duplication
pushover_sent = deque()       # send times in the last hour, for the rate cap

def _pushover_keys():
    token = (os.environ.get("PUSHOVER_TOKEN") or PUSHOVER_TOKEN or "").strip()
    user = (os.environ.get("PUSHOVER_USER") or PUSHOVER_USER or "").strip()
    return token, user

def matched_alert_terms(txt: str) -> list:
    out = []
    for term, pat in zip(alert_terms, alert_patterns):
        try:
            if pat.search(txt or ""):
                out.append(term)
        except Exception:
            pass
    return out

def _bold_terms(escaped_text: str) -> str:
    for pat in alert_patterns:
        try:
            escaped_text = pat.sub(lambda m: f"<b>{m.group(0)}</b>", escaped_text)
        except Exception:
            pass
    return escaped_text

def queue_pushover_alert(data: dict):
    token, user = _pushover_keys()
    if not (token and user):
        return
    now = time.time()
    text = str(data.get("msg_text") or data.get("text") or "").strip()
    flight = str(data.get("flight") or "").strip().upper()
    tail = str(data.get("tail") or "").strip().upper()
    who = flight or tail or str(data.get("hex") or "").upper() or "Unknown"

    key = (who, text[:200])
    last = pushover_recent.get(key)
    if last and now - last < PUSHOVER_DEDUP_MIN * 60:
        return
    pushover_recent[key] = now
    for k in [k for k, t in pushover_recent.items() if now - t > 3600]:
        pushover_recent.pop(k, None)

    terms = matched_alert_terms(text)
    airline = parse_airline(flight) or ""
    title = f"Alert: {who}" + (f" · {airline}" if airline else "")

    lines = []
    if terms:
        lines.append("<b>Matched:</b> " + htmlmod.escape(", ".join(t.upper() for t in terms)))
    if data.get("decoded"):
        lines.append(htmlmod.escape(str(data["decoded"])))
    if text:
        lines.append(_bold_terms(htmlmod.escape(text[:700])))
    facts = []
    if tail and tail != who:
        facts.append(tail)
    src_ = str(data.get("source") or "").upper()
    if src_:
        try:
            facts.append(f"{src_} {float(data['freq']):.3f}" if data.get("freq") is not None else src_)
        except (TypeError, ValueError):
            facts.append(src_)
    if data.get("distance") is not None:
        facts.append(f"{float(data['distance']):.0f} mi {data.get('cardinal') or ''}".strip())
    r = data.get("route")
    if isinstance(r, dict) and r.get("orig"):
        facts.append(f"{r.get('o_iata') or r['orig']} → {r.get('d_iata') or r['dest']}")
    if facts:
        lines.append("<i>" + htmlmod.escape(" · ".join(facts)) + "</i>")
    message = "\n".join(lines) or "(no message text)"
    if len(message) > 1024:
        message = message[:1000] + "…"

    payload = {
        "token": token, "user": user, "title": title[:250], "message": message, "html": "1",
        "priority": str(int(PUSHOVER_PRIORITY)),
        "timestamp": str(int(float(data.get("timestamp") or now))),
    }
    if PUSHOVER_SOUND:
        payload["sound"] = PUSHOVER_SOUND
    cf = canon_flight(flight) if flight else ""
    if cf:
        payload["url"] = f"https://flightaware.com/live/flight/{urllib.parse.quote(cf)}"
        payload["url_title"] = f"{cf} on FlightAware"
    elif tail:
        payload["url"] = f"https://flightaware.com/resources/registration/{urllib.parse.quote(tail)}"
        payload["url_title"] = f"{tail} on FlightAware"
    pushover_queue.append(payload)

def send_pushover(payload: dict):
    """POST one notification. Returns (ok, detail)."""
    body = urllib.parse.urlencode(payload).encode()
    req = urllib.request.Request("https://api.pushover.net/1/messages.json", data=body, method="POST",
                                 headers={"User-Agent": "live-aviation-dashboard"})
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            j = json.loads(resp.read() or b"{}")
            return (j.get("status") == 1), j
    except urllib.error.HTTPError as e:
        try:
            j = json.loads(e.read() or b"{}")
        except Exception:
            j = {}
        return False, {"http": e.code, **j}
    except Exception as e:
        return False, {"error": str(e)}

def pushover_loop():
    while True:
        if not pushover_queue:
            time.sleep(1)
            continue
        now = time.time()
        while pushover_sent and now - pushover_sent[0] > 3600:
            pushover_sent.popleft()
        payload = pushover_queue.popleft()
        nocap = payload.pop("_nocap", False)
        if not nocap and len(pushover_sent) >= PUSHOVER_MAX_PER_HOUR:
            print(f"[PUSHOVER] Hourly cap ({PUSHOVER_MAX_PER_HOUR}) reached; skipped: {payload['title']}")
            continue
        ok, detail = send_pushover(payload)
        if ok:
            pushover_sent.append(now)
            print(f"[PUSHOVER] Sent: {payload['title']}")
        else:
            errs = detail.get("errors") or detail.get("error") or detail
            print(f"[PUSHOVER] Failed: {errs}")
            if detail.get("http") == 429:
                time.sleep(60)
        time.sleep(1)

def pushover_test():
    token, user = _pushover_keys()
    if not (token and user):
        print("Set PUSHOVER_TOKEN and PUSHOVER_USER near the top of this file first.")
        return 1
    ok, detail = send_pushover({
        "token": token, "user": user, "title": "Live Aviation Dashboard",
        "message": "Test notification — alert messages will arrive like this.",
        "priority": str(int(PUSHOVER_PRIORITY)), **({"sound": PUSHOVER_SOUND} if PUSHOVER_SOUND else {}),
    })
    print("Sent! Check your phone." if ok else f"Failed: {detail}")
    return 0 if ok else 1

# =========================
# Emergency squawks
# =========================
EMERG_SQUAWKS = {"7500": "Hijack / unlawful interference", "7600": "Radio failure", "7700": "General emergency"}
EMERG_FLAGS = {"general": "General emergency", "minfuel": "Minimum fuel", "nordo": "Radio failure",
               "unlawful": "Unlawful interference", "downed": "Downed aircraft"}
emerg_state = {}      # hex -> working state (confirmation count, notified)
emergencies = {}      # hex -> public info shown on the page
emerg_events = []     # [ts, ...] confirmed emergencies, for the nightly summary

def _emerg_of(ac):
    sq = str(ac.get("squawk") or "").strip()
    if sq in EMERG_SQUAWKS:
        return sq, EMERG_SQUAWKS[sq]
    flag = str(ac.get("emergency") or "").strip().lower()
    if flag in EMERG_FLAGS:
        return sq or None, EMERG_FLAGS[flag]
    return None, None

def detect_emergencies(active, now):
    seen = set()
    for ac in active:
        code, desc = _emerg_of(ac)
        if not desc:
            continue
        h = str(ac.get("hex") or "").lower()
        if not h:
            continue
        seen.add(h)
        st = emerg_state.get(h)
        if st is None or now - st.get("last", 0) > 30 * 60:
            st = emerg_state[h] = {"n": 0, "first": now, "notified": False}
        st["n"] += 1
        st["last"] = now
        if st["n"] < 2:
            continue   # a single glitchy frame doesn't count; must be seen on two polls in a row
        lat, lon = ac.get("lat"), ac.get("lon")
        dist = card = None
        if isinstance(lat, (int, float)) and isinstance(lon, (int, float)):
            dist = round(calculate_distance_miles(HOME_LAT, HOME_LON, lat, lon), 1)
            card = bearing_to_cardinal(bearing_deg(HOME_LAT, HOME_LON, lat, lon))
        info = {
            "hex": h, "code": code, "desc": desc, "since": st["first"], "last": now, "active": True,
            "flight": str(ac.get("flight") or "").strip() or None, "reg": ac.get("r"), "type": ac.get("t"),
            "alt": ac.get("alt_baro"), "gs": ac.get("gs"), "vr": ac.get("baro_rate") if ac.get("baro_rate") is not None else ac.get("geom_rate"),
            "distance": dist, "cardinal": card,
        }
        emergencies[h] = info
        if not st["notified"]:
            st["notified"] = True
            emerg_events.append(now)
            del emerg_events[:-200]
            who = info["flight"] or info["reg"] or h.upper()
            print(f"[EMERGENCY] {who} {('squawk ' + code + ' ') if code else ''}{desc}"
                  f"{f' ~{dist:.0f} mi {card}' if dist is not None else ''}")
            try:
                queue_emergency_push(ac, info)
            except Exception as e:
                print(f"[PUSHOVER] emergency error: {e}")
    for h, s in emerg_state.items():
        if h not in seen and not s["notified"]:
            s["n"] = 0     # must be consecutive polls; a normal squawk in between starts over
    for h, info in list(emergencies.items()):
        if h not in seen:
            info["active"] = False
            if now - info["last"] > 120:      # keep a cleared emergency visible for 2 minutes
                emergencies.pop(h, None)
    for h in [h for h, s in emerg_state.items() if now - s.get("last", 0) > 30 * 60]:
        emerg_state.pop(h, None)

def queue_emergency_push(ac, info):
    token, user = _pushover_keys()
    if not (token and user):
        return
    who = info["flight"] or info["reg"] or info["hex"].upper()
    title = f"EMERGENCY: {who}" + (f" squawking {info['code']}" if info["code"] else "")
    lines = [f"<b>{htmlmod.escape(info['desc'])}</b>"]
    ident = " · ".join(x for x in [info["flight"], info["reg"], info["type"]] if x)
    if ident:
        lines.append(htmlmod.escape(ident))
    perf = []
    alt = info["alt"]
    if alt == "ground":
        perf.append("on the ground")
    elif isinstance(alt, (int, float)):
        perf.append(f"{int(alt):,} ft")
    if isinstance(info["vr"], (int, float)) and abs(info["vr"]) >= 300:
        perf.append(f"{'↑' if info['vr'] > 0 else '↓'}{abs(int(info['vr'])):,} fpm")
    if isinstance(info["gs"], (int, float)):
        perf.append(f"{int(info['gs'])} kt")
    if perf:
        lines.append(htmlmod.escape(" · ".join(perf)))
    if info["distance"] is not None:
        lines.append(htmlmod.escape(f"{info['distance']:.0f} mi {info['cardinal'] or ''} of home".strip()))
    try:
        r = get_route(info["hex"], info["reg"], None, info["flight"], pos=pos_of(ac))
        if r:
            lines.append(htmlmod.escape(f"Route {r.get('o_iata') or r['orig']} → {r.get('d_iata') or r['dest']}"))
    except Exception:
        pass
    pr = int(PUSHOVER_EMERGENCY_PRIORITY)
    payload = {
        "token": token, "user": user, "title": title[:250], "message": "\n".join(lines), "html": "1",
        "priority": str(pr), "url": f"https://globe.adsbexchange.com/?icao={info['hex']}",
        "url_title": "Track on ADS-B Exchange", "_nocap": True,
    }
    if pr >= 2:
        payload.update({"retry": "60", "expire": "1800"})
    if PUSHOVER_EMERGENCY_SOUND:
        payload["sound"] = PUSHOVER_EMERGENCY_SOUND
    pushover_queue.appendleft(payload)    # jump the queue

# =========================
# Coverage (farthest ACARS / VDLM2 contact per bearing)
# =========================
COVERAGE_PATH = os.path.join(BASE_DIR, "coverage.json")
coverage = {"acars": {}, "vdlm2": {}}   # mode -> {bin: [dist, lat, lon, ts, flight]}
coverage_dirty = False

def load_coverage():
    global coverage
    try:
        if os.path.exists(COVERAGE_PATH):
            with open(COVERAGE_PATH, "r") as f:
                data = json.load(f)
            for mode in ("acars", "vdlm2"):
                coverage[mode] = {str(k): v for k, v in (data.get(mode) or {}).items()}
            n = sum(len(v) for v in coverage.values())
            print(f"[COVERAGE] Loaded {n} coverage points")
    except Exception as e:
        print(f"[COVERAGE] Load failed: {e}")

def save_coverage():
    global coverage_dirty
    if not coverage_dirty:
        return
    try:
        _atomic_write_json(COVERAGE_PATH, coverage)
        coverage_dirty = False
    except Exception as e:
        print(f"[COVERAGE] Save failed: {e}")

async def periodic_coverage_save():
    while True:
        await asyncio.sleep(300)
        save_coverage()

def note_coverage(mode, lat, lon, dist, brg, flight=None):
    """Remember the farthest point a message of this mode was received from, per bearing bin."""
    global coverage_dirty
    mode = str(mode or "").lower()
    if mode not in coverage or not isinstance(dist, (int, float)) or dist > COVERAGE_MAX_MI or dist < 1:
        return
    b = str(int((brg % 360) // COVERAGE_BIN_DEG))
    cur = coverage[mode].get(b)
    if cur is None or dist > cur[0]:
        coverage[mode][b] = [round(dist, 1), round(lat, 4), round(lon, 4), int(time.time()),
                             (str(flight).strip().upper() or None) if flight else None]
        coverage_dirty = True

def coverage_payload() -> bytes:
    out = {"bin_deg": COVERAGE_BIN_DEG}
    for mode in ("acars", "vdlm2"):
        out[mode] = sorted(([int(b)] + v for b, v in coverage[mode].items()), key=lambda r: r[0])
    return json.dumps(out).encode()

# =========================
# Nightly station summary
# =========================
SUMMARY_LAST_PATH = os.path.join(BASE_DIR, "summary_last.txt")

def _local_midnight(ts):
    lt = time.localtime(ts)
    return time.mktime((lt.tm_year, lt.tm_mon, lt.tm_mday, 0, 0, 0, 0, 0, -1))

def build_summary(start, end) -> tuple:
    con = sqlite3.connect(DB_PATH, timeout=10)
    try:
        q = con.execute
        total, n_acars, n_vdlm2, n_ver, n_alert = q(
            """SELECT COUNT(*), SUM(source='acars'), SUM(source='vdlm2'), SUM(verified), SUM(alert)
               FROM messages WHERE ts >= ? AND ts < ?""", (start, end)).fetchone()
        far = q("""SELECT flight, tail, distance, source FROM messages WHERE ts >= ? AND ts < ? AND distance IS NOT NULL
                   ORDER BY distance DESC LIMIT 1""", (start, end)).fetchone()
        busy = q("""SELECT CAST(strftime('%H', ts, 'unixepoch', 'localtime') AS INTEGER) AS h, COUNT(*) AS c
                    FROM messages WHERE ts >= ? AND ts < ? GROUP BY h ORDER BY c DESC LIMIT 1""", (start, end)).fetchone()
        top = q("""SELECT airline, COUNT(*) FROM messages WHERE ts >= ? AND ts < ? AND airline IS NOT NULL
                   GROUP BY airline ORDER BY 2 DESC LIMIT 1""", (start, end)).fetchone()
    finally:
        con.close()
    total, n_acars, n_vdlm2, n_ver, n_alert = [int(x or 0) for x in (total, n_acars, n_vdlm2, n_ver, n_alert)]
    n_emerg = sum(1 for t in emerg_events if start <= t < end)

    def hr(h):
        return time.strftime("%-I %p", time.struct_time((2000, 1, 1, h, 0, 0, 0, 1, -1))).lstrip("0")

    day = time.strftime("%a %b %-d", time.localtime(start))
    lines = [f"<b>Messages:</b> {total:,}  (ACARS {n_acars:,} · VDLM2 {n_vdlm2:,})"]
    lines.append(f"<b>Verified:</b> {(n_ver / total * 100) if total else 0:.0f}%  ({n_ver:,} matched to ADS-B)")
    lines.append(f"<b>Alerts:</b> {n_alert:,}")
    if far:
        who = (far[0] or far[1] or "unknown").strip()
        lines.append(f"<b>Farthest verified contact:</b> {htmlmod.escape(who)} · {far[2]:.0f} mi ({str(far[3] or '').upper()})")
    if busy:
        lines.append(f"<b>Busiest hour:</b> {hr(busy[0])}–{hr((busy[0] + 1) % 24)}  ({busy[1]:,} messages)")
    if top:
        lines.append(f"<b>Top airline:</b> {htmlmod.escape(top[0])} ({top[1]:,})")
    lines.append(f"<b>Emergencies:</b> {n_emerg if n_emerg else 'none'}")
    if not total:
        lines.append("<i>No messages received today — check the decoders.</i>")
    return f"Station summary · {day}", "\n".join(lines)

async def send_summary(now=None, force=False) -> bool:
    now = now or time.time()
    rows = db_buffer[:]
    del db_buffer[:len(rows)]
    await asyncio.to_thread(db_write, rows)
    start = _local_midnight(now)
    title, body = await asyncio.to_thread(build_summary, start, now + 1)
    token, user = _pushover_keys()
    if not (token and user):
        print(f"[SUMMARY] {title}\n{body}\n[SUMMARY] (Pushover keys not set; not sent)")
        return False
    ok, detail = await asyncio.to_thread(send_pushover, {
        "token": token, "user": user, "title": title, "message": body, "html": "1",
        "priority": str(int(PUSHOVER_SUMMARY_PRIORITY)),
    })
    print(f"[SUMMARY] {'Sent' if ok else 'Failed'}: {title}" + ("" if ok else f" ({detail})"))
    return ok

async def periodic_summary():
    if not SUMMARY_ENABLED:
        return
    try:
        hh, mm = [int(x) for x in str(SUMMARY_TIME).split(":")[:2]]
    except Exception:
        print(f"[SUMMARY] Bad SUMMARY_TIME {SUMMARY_TIME!r}; expected like \"21:00\". Summary disabled.")
        return
    print(f"[SUMMARY] Daily summary at {hh:02d}:{mm:02d}")
    while True:
        try:
            now = time.time()
            lt = time.localtime(now)
            today = time.strftime("%Y-%m-%d", lt)
            due = (lt.tm_hour, lt.tm_min) >= (hh, mm)
            last = ""
            if os.path.exists(SUMMARY_LAST_PATH):
                with open(SUMMARY_LAST_PATH) as f:
                    last = f.read().strip()
            if due and last != today:
                with open(SUMMARY_LAST_PATH, "w") as f:
                    f.write(today)        # mark first so a failure can't cause a flood of retries
                await send_summary(now)
        except Exception as e:
            print(f"[SUMMARY] error: {e}")
        await asyncio.sleep(30)

# =========================
# Flight timeline log + takeoff/landing detector
# =========================
flight_log = {}        # "F:AAL123" or "T:N123AB" -> {"msgs": deque, "last", "flight", "tail", "hex"}
ap_state = {}          # hex -> detector working state
ap_events = {}         # hex -> latest departure/arrival event (drives the badge)
ap_history = {}        # hex -> [events] for the timeline
_flight_log_n = 0

OOOI_EVENTS = {
    "OUT": {"QA", "QE", "QG", "QH", "QP", "QT"},
    "OFF": {"QB", "QF", "QQ"},
    "ON":  {"QC", "QK", "QR"},
    "IN":  {"QD", "QS"},
}
OOOI_BY_LABEL = {lab: ev for ev, labs in OOOI_EVENTS.items() for lab in labs}
OOOI_TIME_RE = regex.compile(r'^[A-Z]{4}(?:[A-Z]{4})?(\d{4})')

def flight_key(flight, tail):
    c = canon_flight(flight)
    if c:
        return "F:" + c
    t = _norm_reg(tail)
    return "T:" + t if len(t) >= 3 else None

def _oooi_of(data):
    ev = OOOI_BY_LABEL.get(str(data.get("label") or "").strip())
    if not ev:
        return None
    m = OOOI_TIME_RE.match(str(data.get("msg_text") or "").strip().upper())
    hhmm = None
    if m:
        hh, mm = int(m.group(1)[:2]), int(m.group(1)[2:])
        if hh < 24 and mm < 60:
            hhmm = m.group(1)
    return {"ev": ev, "hhmm": hhmm}

def log_flight_message(data):
    global _flight_log_n
    k = flight_key(data.get("flight"), data.get("tail"))
    if not k:
        return
    now = time.time()
    fl = flight_log.get(k)
    if fl is None:
        fl = flight_log[k] = {"msgs": deque(maxlen=250), "last": now, "flight": None, "tail": None, "hex": None}
    fl["last"] = now
    fl["flight"] = str(data.get("flight") or "").strip().upper() or fl["flight"]
    fl["tail"] = data.get("tail") or fl["tail"]
    fl["hex"] = data.get("matched_hex") or data.get("hex") or fl["hex"]
    entry = {
        "id": data.get("id"), "ts": data.get("timestamp") or now, "source": data.get("source"),
        "freq": data.get("freq"), "label": data.get("label"), "label_name": data.get("label_name"),
        "msg_type": data.get("msg_type"), "decoded": data.get("decoded"),
        "text": str(data.get("msg_text") or data.get("text") or "")[:800],
        "distance": data.get("distance"), "cardinal": data.get("cardinal"),
        "alert": bool(data.get("alert")), "alt": data.get("parsed_alt_ft"),
        "noise": bool(data.get("noise")),
    }
    o = _oooi_of(data)
    if o:
        entry["oooi"] = o
    fl["msgs"].append(entry)
    _flight_log_n += 1
    if _flight_log_n % 500 == 0:
        cutoff = now - FLIGHT_LOG_HOURS * 3600
        for kk in [kk for kk, v in flight_log.items() if v["last"] < cutoff]:
            flight_log.pop(kk, None)
        for h in [h for h, evs in ap_history.items() if not evs or evs[-1]["ts"] < cutoff]:
            ap_history.pop(h, None)

def _hhmm_to_epoch(hhmm, ref_ts):
    """OOOI times are HHMM UTC with no date: put them on the day of the message."""
    g = time.gmtime(ref_ts)
    t = calendar.timegm((g.tm_year, g.tm_mon, g.tm_mday, int(hhmm[:2]), int(hhmm[2:]), 0, 0, 0, 0))
    if t > ref_ts + 3600:
        t -= 86400
    elif t < ref_ts - 23 * 3600:
        t += 86400
    return t

def detect_airport_events(active, now):
    """Departures: rapid climb near the field (or ground -> airborne). Arrivals: rapid descent toward it (or airborne -> ground)."""
    seen = set()
    for ac in active:
        h = str(ac.get("hex") or "").lower()
        lat, lon = ac.get("lat"), ac.get("lon")
        if not h or not isinstance(lat, (int, float)) or not isinstance(lon, (int, float)):
            continue
        seen.add(h)
        alt_raw = ac.get("alt_baro")
        on_ground = alt_raw == "ground"
        alt = alt_raw if isinstance(alt_raw, (int, float)) else None
        st = ap_state.get(h)
        if st is None:
            st = ap_state[h] = {"cand": None, "n": 0, "prev_alt": None, "prev_ts": None, "prev_ground": None, "prev_dist": None, "seen": now}
        st["seen"] = now

        vr = ac.get("baro_rate")
        if not isinstance(vr, (int, float)):
            vr = ac.get("geom_rate")
        if not isinstance(vr, (int, float)):
            vr = None
            if alt is not None and st["prev_alt"] is not None and st["prev_ts"] and now - st["prev_ts"] >= 2:
                vr = (alt - st["prev_alt"]) / (now - st["prev_ts"]) * 60

        near = None
        for ap in AIRPORT_WATCH:
            d = calculate_distance_miles(ap["lat"], ap["lon"], lat, lon)
            if d <= AP_RADIUS_MI:
                near = (ap, d)
                break

        cand = None
        quick = False
        if near:
            ap, d = near
            agl = 0 if on_ground else (alt - ap["elev"] if alt is not None else None)
            if st["prev_ground"] is True and not on_ground and alt is not None:
                cand, quick = "departure", True
            elif st["prev_ground"] is False and on_ground:
                cand, quick = "arrival", True
            elif agl is not None and agl <= AP_MAX_AGL and vr is not None and not on_ground:
                moving_away = st["prev_dist"] is None or d >= st["prev_dist"] - 0.05
                closing = st["prev_dist"] is None or d <= st["prev_dist"] + 0.05
                if vr >= AP_CLIMB_FPM and moving_away:
                    cand = "departure"
                elif vr <= AP_DESCENT_FPM and closing:
                    cand = "arrival"

            if cand and cand == st["cand"]:
                st["n"] += 1
            elif cand:
                st["cand"], st["n"] = cand, (2 if quick else 1)
            else:
                st["cand"], st["n"] = None, 0

            if cand and st["n"] >= 2:
                last = ap_events.get(h)
                if not last or last["type"] != cand or now - last["ts"] > 1200:
                    ev = {
                        "type": cand, "code": ap["code"], "name": ap["name"], "ts": now,
                        "agl": int(agl) if isinstance(agl, (int, float)) else None,
                        "vr": int(vr) if isinstance(vr, (int, float)) else None,
                        "flight": str(ac.get("flight") or "").strip() or None, "reg": ac.get("r"),
                    }
                    ap_events[h] = ev
                    ap_history.setdefault(h, []).append(ev)
                    del ap_history[h][:-10]
                    who = ev["flight"] or ev["reg"] or h.upper()
                    print(f"[AIRPORT] {who} {'departing' if cand == 'departure' else 'arriving'} {ap['code']} "
                          f"({ev['agl'] if ev['agl'] is not None else '?'} ft AGL, {ev['vr'] if ev['vr'] is not None else '?'} fpm)")
            st["prev_dist"] = d
        else:
            st["cand"], st["n"], st["prev_dist"] = None, 0, None

        st["prev_alt"] = alt
        st["prev_ts"] = now
        st["prev_ground"] = on_ground if (alt is not None or on_ground) else st["prev_ground"]

    for h in [h for h, s in ap_state.items() if now - s["seen"] > 300]:
        ap_state.pop(h, None)
    for h in [h for h, e in ap_events.items() if now - e["ts"] > AP_BADGE_SEC]:
        ap_events.pop(h, None)

def flight_payload(flight=None, tail=None, hex_id=None) -> dict:
    hex_id = str(hex_id or "").lower() or None
    ac = {}
    if hex_id and adsb_aircraft.get(hex_id):
        ac = adsb_aircraft[hex_id]["data"]
    flight = (flight or str(ac.get("flight") or "").strip()) or None
    tail = tail or ac.get("r") or ac.get("reg")

    fl = None
    for k in (flight_key(flight, None), flight_key(None, tail)):
        if k and flight_log.get(k):
            fl = flight_log[k]
            break
    if fl and not hex_id:
        hex_id = fl.get("hex")
        if hex_id and adsb_aircraft.get(hex_id):
            ac = adsb_aircraft[hex_id]["data"]
    msgs = sorted(list(fl["msgs"]) if fl else [], key=lambda m: m.get("ts") or 0)

    oooi = {}
    for m in msgs:
        o = m.get("oooi")
        if not o:
            continue
        ts = _hhmm_to_epoch(o["hhmm"], m["ts"]) if o.get("hhmm") else m["ts"]
        oooi[o["ev"]] = {"ts": ts, "reported": bool(o.get("hhmm")), "msg_ts": m["ts"]}
    # A new OUT after an older IN means a new leg: drop the stale ON/IN.
    if "OUT" in oooi:
        for ev in ("OFF", "ON", "IN"):
            if ev in oooi and oooi[ev]["ts"] < oooi["OUT"]["ts"] - 300:
                oooi.pop(ev)

    profile = []
    if hex_id and trails.get(hex_id):
        profile = [[p[3], p[2]] for p in list(trails[hex_id]["pts"])]

    route = None
    why = {}
    try:
        route = get_route(hex_id, tail, flight, ac.get("flight"), pos=pos_of(ac), why=why)
    except Exception:
        pass

    return {
        "flight": (fl or {}).get("flight") or (flight.upper() if flight else None),
        "tail": tail or (fl or {}).get("tail"),
        "hex": hex_id, "live": bool(ac),
        "aircraft": {k: ac.get(k) for k in ("t", "category", "alt_baro", "gs", "track", "baro_rate", "geom_rate", "squawk", "r", "flight", "desc")} if ac else None,
        "route": route,
        "route_rejected": None if route else why.get("rejected"),
        "oooi": oooi,
        "airport_events": ap_history.get(hex_id, []) if hex_id else [],
        "profile": profile,
        "messages": msgs,
    }

# =========================
# ADS-B poller (runs in a background thread)
# =========================
def adsb_poll_loop():
    """Poll tar1090 continuously so matching and the watch list work even with no browser open."""
    global adsb_aircraft, adsb_snapshot, adsb_last_sum, adsb_last_t, adsb_rate
    was_ok = None
    while True:
        started = time.time()
        try:
            with urllib.request.urlopen(TAR1090_URL, timeout=4) as resp:
                j = json.loads(resp.read())
            now = time.time()
            incoming = j.get("aircraft", []) or []

            # Keep recently-seen aircraft briefly; drop anything stale.
            new_map = {h: info for h, info in adsb_aircraft.items() if now - info["last_seen"] <= ADSB_TIMEOUT}
            active = []
            sum_msgs = 0

            for ac in incoming:
                hex_id = (ac.get("hex") or "").lower()
                if not hex_id:
                    continue

                m = ac.get("messages")
                if m is None: m = ac.get("msgs")
                if isinstance(m, (int, float)): sum_msgs += int(m)

                seen_pos = ac.get("seen_pos")
                seen = ac.get("seen", 0)
                fresh = (seen_pos <= 58.5) if seen_pos is not None else (seen <= 58.5)
                if fresh:
                    new_map[hex_id] = {"data": ac, "last_seen": now}
                    active.append(ac)

            if adsb_last_sum is not None and adsb_last_t is not None:
                dt = max(0.001, now - adsb_last_t)
                adsb_rate = max(0, sum_msgs - adsb_last_sum) / dt
            adsb_last_sum = sum_msgs
            adsb_last_t = now

            adsb_aircraft = new_map  # atomic swap; readers never see a half-updated dict
            update_trails(active, now)
            try:
                detect_airport_events(active, now)
            except Exception as e:
                print(f"[AIRPORT] detector error: {e}")
            events = {h: e for h, e in ap_events.items() if h in new_map}
            try:
                detect_emergencies(active, now)
            except Exception as e:
                print(f"[EMERGENCY] detector error: {e}")
            routes, rejects = {}, {}
            for ac in active:
                try:
                    why = {}
                    hx = str(ac.get("hex") or "").lower()
                    r = get_route(ac.get("hex"), ac.get("r") or ac.get("reg"), None, ac.get("flight"), pos=pos_of(ac), why=why)
                    if r:
                        routes[hx] = r
                    elif why.get("rejected"):
                        rejects[hx] = why["rejected"]
                except Exception:
                    pass
            adsb_snapshot = json.dumps({"aircraft": active, "now": j.get("now", now), "routes": routes,
                                        "route_rejects": rejects, "events": events,
                                        "emergencies": emergencies}).encode()
            stream_status["adsb"] = True
            if was_ok is not True:
                print(f"[ADS-B] Connected {TAR1090_URL}")
            was_ok = True
        except Exception as e:
            stream_status["adsb"] = False
            if was_ok is not False:
                print(f"[ADS-B] Poll error ({TAR1090_URL}): {e}")
            was_ok = False
        time.sleep(max(0.5, ADSB_POLL_SEC - (time.time() - started)))

# =========================
# WebSocket server
# =========================
clients = set()

def build_status():
    a, v, t, ad = get_rates_now()
    now = time.time()
    for h in [h for h, ts in recent_verified.items() if (now - ts) > RECENT_VERIFY_WINDOW]:
        del recent_verified[h]
    verified_list = list(recent_verified.keys())
    watch_list = compute_watch_list()
    return {
        "type": "status",
        "acars": stream_status["acars"],
        "vdlm2": stream_status["vdlm2"],
        "adsb": stream_status["adsb"],
        "uptime": format_uptime(),
        "server_time": now,
        "total_messages": total_message_count,
        "matched_messages": matched_message_count,
        "freq_counts": frequency_counts,
        "distance_bins": distance_bins,
        "airline_counts": airline_counts,
        "acars_rate": a, "vdlm2_rate": v, "total_radio_rate": t, "adsb_rate": ad,
        "verified_hexes": verified_list,
        "watch": watch_list[0] if watch_list else None,
        "watch_list": watch_list,
        "alert_terms": alert_terms,
        "alert_count": len(alerts_history),
    }

async def _send_all(pkt: str):
    if clients:
        await asyncio.gather(*[c.send(pkt) for c in list(clients)], return_exceptions=True)

async def ws_handler(websocket, path=None):
    # `path` is optional: newer websockets versions call handlers with one argument.
    clients.add(websocket)
    try:
        await websocket.send(json.dumps(build_status()))

        if stored_messages or alerts_history:
            # Combine, de-duplicate by (timestamp, text), sort by timestamp, keep newest 200.
            combined = []
            seen = set()
            for msg in (alerts_history or []) + stored_messages[-MAX_MESSAGES:]:
                if not isinstance(msg, dict):
                    continue
                ts = int(msg.get("timestamp") or msg.get("ts") or 0)
                textish = (msg.get("text") or msg.get("raw") or msg.get("message") or msg.get("msg_text") or "")[:200]
                key = (ts, textish)
                if key in seen:
                    continue
                seen.add(key)
                combined.append(msg)
            combined.sort(key=lambda m: int(m.get("timestamp") or m.get("ts") or 0))
            await websocket.send(json.dumps({"type": "history", "messages": combined[-200:]}))
            await websocket.send(json.dumps({"type": "alert_history", "messages": alerts_history or []}))

        async for message in websocket:
            try:
                data = json.loads(message)
                if data.get("type") == "ping":
                    await websocket.send(json.dumps(build_status()))
                elif data.get("type") == "alert_star":
                    if star_alert(str(data.get("aid") or ""), data.get("starred")):
                        await _send_all(json.dumps({"type": "alert_history", "messages": alerts_history}))
                elif data.get("type") == "alert_terms_set":
                    try:
                        terms = save_alert_terms(data.get("terms") if isinstance(data.get("terms"), list) else [])
                        await websocket.send(json.dumps({"type": "alert_terms_saved", "ok": True, "count": len(terms)}))
                    except Exception as e:
                        print(f"[ALERTS] Saving keywords failed: {e}")
                        await websocket.send(json.dumps({"type": "alert_terms_saved", "ok": False, "error": str(e)}))
                    await broadcast_status()
                elif data.get("type") == "alerts_reset":
                    reset_alerts()
                    await _send_all(json.dumps({"type": "alert_history", "messages": alerts_history, "reset": True}))
                    await broadcast_status()
            except json.JSONDecodeError:
                pass
    except Exception:
        pass
    finally:
        clients.discard(websocket)

async def broadcast_status():
    await _send_all(json.dumps(build_status()))

async def periodic_status_push():
    # Keeps uptime, rates and link lights live even when the radios are quiet.
    while True:
        await asyncio.sleep(STATUS_PUSH_SEC)
        try:
            await broadcast_status()
        except Exception as e:
            print(f"[STATUS] push failed: {e}")

async def broadcast_notify(info: dict):
    """Send a single notification to all clients."""
    await _send_all(json.dumps({"type": "notify", **info}))

# =========================
# Plain-English decoding
# =========================
LABEL_NAMES = {
    "_d": "General response (no content)",
    "00": "Emergency situation report",
    "2Z": "Progress report",
    "5U": "Weather request",
    "5Z": "Airline-designated downlink",
    "80": "Airline-defined message",
    "A6": "ADS-C request",
    "AA": "CPDLC uplink",
    "B6": "ADS-C report",
    "BA": "CPDLC downlink",
    "H1": "FMS / onboard system message",
    "Q0": "Link test",
    "QA": "OUT report", "QB": "OFF report", "QC": "ON report", "QD": "IN report",
    "QE": "OUT / fuel report", "QF": "OFF / destination report", "QG": "OUT / return-IN report",
    "QH": "OUT report", "QK": "Landing report", "QL": "Arrival report",
    "QM": "Arrival information report", "QN": "Diversion report", "QP": "OUT report",
    "QQ": "OFF report", "QR": "ON report", "QS": "IN report", "QT": "OUT / return-IN report",
    "SA": "Media advisory (link status)",
    "SQ": "Squitter (ground station beacon)",
}
NOISE_LABELS = {"_d", "Q0", "SQ", "SA"}

H1_PREFIXES = [
    ("#CFB", "Maintenance fault report"),
    ("#DFB", "Aircraft performance / ACMS report"),
    ("#M1B", "FMS message"), ("#M2B", "FMS message"), ("#M3B", "FMS message"),
]

AIRPORT_PAIR_RE = regex.compile(r'^([KCPMT][A-Z]{3})([KCPMT][A-Z]{3})?')
WX_RE           = regex.compile(r'\b(METAR|SPECI|TAF)\s+([A-Z]{4})\b')
AIRPORT_RE      = regex.compile(r'\b([KCPM][A-Z]{3})\b')

def _find_key(obj, key, depth=0):
    """Find the first dict value stored under `key` anywhere inside obj (depth-limited)."""
    if depth > 6:
        return None
    if isinstance(obj, dict):
        if key in obj:
            return obj[key]
        for v in obj.values():
            r = _find_key(v, key, depth + 1)
            if r is not None:
                return r
    elif isinstance(obj, list):
        for v in obj:
            r = _find_key(v, key, depth + 1)
            if r is not None:
                return r
    return None

def _find_latlon(obj, depth=0):
    if depth > 8:
        return None
    if isinstance(obj, dict):
        lat, lon = obj.get("lat"), obj.get("lon")
        if isinstance(lat, (int, float)) and isinstance(lon, (int, float)) and -90 <= lat <= 90 and -180 <= lon <= 180:
            alt = obj.get("alt")
            return float(lat), float(lon), (alt if isinstance(alt, (int, float)) else None)
        for v in obj.values():
            r = _find_latlon(v, depth + 1)
            if r:
                return r
    elif isinstance(obj, list):
        for v in obj:
            r = _find_latlon(v, depth + 1)
            if r:
                return r
    return None

def _scan_arinc622(raw: dict, out: dict):
    """Pick up libacars-decoded FANS data (ADS-C positions, CPDLC) when the decoder provides it."""
    try:
        a = _find_key(raw, "arinc622")
        if not isinstance(a, dict):
            return
        adsc = a.get("adsc")
        if isinstance(adsc, dict):
            pos = _find_latlon(adsc)
            if pos and out.get("pos_lat") is None:
                lat, lon, alt = pos
                out["pos_lat"], out["pos_lon"] = round(lat, 6), round(lon, 6)
                if alt is not None and out.get("parsed_alt_ft") is None:
                    out["parsed_alt_ft"] = int(alt)
                s = f"ADS-C position report: {abs(lat):.3f}° {'S' if lat < 0 else 'N'}, {abs(lon):.3f}° {'W' if lon < 0 else 'E'}"
                if alt is not None:
                    s += f" • Alt {int(alt):,} ft"
                out["_a622"] = ("ADS-C position report", s)
            else:
                out["_a622"] = ("ADS-C report", "ADS-C (automatic surveillance) report")
        elif isinstance(a.get("cpdlc"), dict):
            out["_a622"] = ("CPDLC message", "CPDLC controller–pilot datalink message")
    except Exception as e:
        print(f"[DECODE] arinc622 error: {e}")

def _is_free_text(text: str) -> bool:
    if len(text) < 12:
        return False
    letters = sum(c.isalpha() or c.isspace() for c in text)
    words = regex.findall(r'[A-Za-z]{3,}', text)
    return letters / len(text) > 0.75 and len(words) >= 3

def decode_message(out: dict):
    """Attach label_name, msg_type, decoded (plain-English summary) and noise flag."""
    label = str(out.get("label") or "").strip()
    text = str(out.get("msg_text") or "").strip()
    up = text.upper()
    name = LABEL_NAMES.get(label)
    if name:
        out["label_name"] = name

    mtype, dec = None, None
    a622 = out.pop("_a622", None)
    xid = out.pop("_xid", False)
    link = out.pop("_link", False)

    if out.get("parsed_ground_station"):
        mtype, dec = "Ground station squitter", out.get("parsed_summary")
    elif a622:
        mtype, dec = a622
    elif out.get("pos_lat") is not None and out.get("parsed_summary"):
        mtype, dec = "Position report", out.get("parsed_summary")
    elif label.startswith("Q") and label != "Q0" and name:
        mtype = name
        m = AIRPORT_PAIR_RE.match(up)
        if m and m.group(2):
            dec = f"{name}: {m.group(1)} → {m.group(2)}"
        elif m:
            dec = f"{name}: {m.group(1)}"
        else:
            dec = name
    elif WX_RE.search(up):
        found = []
        for kind, apt in WX_RE.findall(up):
            item = f"{kind} {apt}"
            if item not in found:
                found.append(item)
        mtype, dec = "Weather", "Weather data: " + ", ".join(found[:4])
    elif label == "5U":
        apts = list(dict.fromkeys(AIRPORT_RE.findall(up)))[:4]
        mtype, dec = "Weather request", "Weather request" + (f" for {', '.join(apts)}" if apts else "")
    elif "ATIS" in up:
        apts = list(dict.fromkeys(AIRPORT_RE.findall(up)))[:2]
        mtype, dec = "ATIS", "ATIS (airport information)" + (f" for {', '.join(apts)}" if apts else "")
    elif "FPN/" in up:
        dep = regex.search(r'DA:([A-Z]{4})', up)
        arr = regex.search(r'AA:([A-Z]{4})', up)
        mtype = "Flight plan"
        dec = "Flight plan" + (f": {dep.group(1)}" if dep else "") + (f" → {arr.group(1)}" if arr else "")
    elif "REQPWI" in up:
        mtype, dec = "Wind data request", "Request for predicted winds"
    elif "PWI/" in up:
        mtype, dec = "Wind data", "Predicted wind data (uplink)"
    else:
        for prefix, desc in H1_PREFIXES:
            if up.startswith(prefix) or up.startswith("- " + prefix):
                mtype, dec = desc, desc
                break

    if not mtype:
        if xid:
            mtype, dec = "VDL2 link management", "VDL2 link management (XID) — ground station handoff"
        elif link and not label:
            mtype = "VDL2 link-layer frame"
        elif text and _is_free_text(text):
            mtype = "Free text"
        elif name:
            mtype = name
        elif not text:
            mtype = "No content"
        else:
            mtype = f"Label {label}" if label else "Other"

    out["msg_type"] = mtype
    if dec:
        out["decoded"] = dec
    out["noise"] = bool(
        label in NOISE_LABELS or xid or (link and not label)
        or (not text and out.get("pos_lat") is None)
    )

# =========================
# Normalizers
# =========================
def _clean_tail(v):
    s = str(v or "").strip().lstrip(".").upper()
    return s or None

def normalize_acars(obj: dict) -> dict:
    out = {
        "source": "acars",
        "freq": obj.get("freq"),
        "timestamp": obj.get("timestamp"),
        "flight": obj.get("flight"),
        "tail": _clean_tail(obj.get("tail")),
        "label": obj.get("label"),
        "block_id": obj.get("block_id"),
    }
    out["msg_text"] = (
        obj.get("msg_text")
        or obj.get("text")
        or obj.get("message")
        or obj.get("msg")
        or obj.get("payload")
        or obj.get("summary")
    )
    _apply_text_parsers(out)
    _scan_arinc622(obj, out)
    decode_message(out)
    return out

def _apply_text_parsers(out: dict):
    text = out.get("msg_text") or ""
    try:
        pr = parse_acars_posn(text)
        if pr:
            out.update(pr)
    except Exception as e:
        print(f"[POS] parse error: {e}")
    try:
        gs = parse_ground_station_squitter(text)
        if gs:
            out.update(gs)
    except Exception as e:
        print(f"[GS] parse error: {e}")

TEXT_KEYS = ("text", "txt", "cmd", "info", "data", "payload", "summary", "message", "raw", "msg", "note", "desc")

def normalize_vdlm2(obj: dict) -> dict:
    """
    Best-effort normalization for VDLM2 (dumpvdl2 JSON): prefer the embedded ACARS block,
    then fall back to collecting readable text and a plausible flight id.
    """
    v = obj.get("vdl2", obj)

    out = {
        "source": "vdlm2",
        "freq": None,
        "timestamp": None,
        "msg_text": None,
        "flight": None,
        "tail": None,
    }

    # Frequency
    try:
        freq = v.get("freq")
        if isinstance(freq, (int, float)):
            out["freq"] = float(freq) / 1_000_000.0 if freq > 1_000_000 else float(freq)
    except Exception:
        pass

    # Timestamp
    try:
        t = v.get("t", {})
        if isinstance(t, dict) and isinstance(t.get("sec"), (int, float)):
            out["timestamp"] = float(t["sec"])
        elif isinstance(v.get("ts"), (int, float)):
            out["timestamp"] = float(v["ts"])
        elif isinstance(v.get("time"), (int, float)):
            out["timestamp"] = float(v["time"])
        elif isinstance(obj.get("timestamp"), (int, float)):
            out["timestamp"] = float(obj["timestamp"])
    except Exception:
        pass

    avlc = v.get("avlc", {}) if isinstance(v.get("avlc"), dict) else {}

    # Hex (src addr)
    try:
        src = avlc.get("src", {})
        if isinstance(src, dict) and isinstance(src.get("addr"), str):
            out["hex"] = src["addr"].lower()
    except Exception:
        pass

    text_candidates = []

    # Embedded ACARS (most VDLM2 traffic carries this)
    acars = avlc.get("acars") if isinstance(avlc.get("acars"), dict) else {}
    if acars:
        if isinstance(acars.get("flight"), str) and acars["flight"].strip():
            out["flight"] = acars["flight"].strip().upper()
        out["tail"] = _clean_tail(acars.get("reg")) or out["tail"]
        if acars.get("label"):
            out["label"] = acars.get("label")
        if acars.get("blk_id") or acars.get("block_id"):
            out["block_id"] = acars.get("blk_id") or acars.get("block_id")
        for k in ("msg_text", "text"):
            if isinstance(acars.get(k), str) and acars[k].strip():
                text_candidates.append(acars[k])

    for container in (v, avlc):
        for k in TEXT_KEYS:
            val = container.get(k)
            if isinstance(val, str) and val.strip():
                text_candidates.append(val)

    miam = avlc.get("miam", {}) if isinstance(avlc.get("miam"), dict) else {}
    for k in ("text", "txt", "info", "summary"):
        mv = miam.get(k)
        if isinstance(mv, str) and mv.strip():
            text_candidates.append(mv)

    # Fallback: sweep any short-ish strings
    if not text_candidates:
        text_candidates.extend(_collect_strings(v))

    out["msg_text"] = _coalesce_unique(text_candidates, sep=" | ") or None
    _apply_text_parsers(out)

    # Flight extraction (if the ACARS block didn't provide one)
    if not out["flight"]:
        xid = avlc.get("xid", {}) if isinstance(avlc.get("xid"), dict) else {}
        for k in ("flight", "flight_id", "callsign", "type_descr"):
            fv = xid.get(k)
            if isinstance(fv, str) and fv.strip():
                out["flight"] = fv.strip().upper()
                break

    if not out["flight"]:
        for k in ("flight", "callsign", "fid"):
            fv = avlc.get(k)
            if isinstance(fv, str) and fv.strip():
                out["flight"] = fv.strip().upper()
                break

    if not out["flight"] and not acars and out["msg_text"]:
        m = regex.search(r"\b([A-Z]{2,3}\s?\d{1,4})\b", out["msg_text"])
        if m:
            out["flight"] = m.group(1).replace(" ", "").upper()

    if not acars:
        out["_link"] = True
        if isinstance(avlc.get("xid"), dict):
            out["_xid"] = True
    _scan_arinc622(obj, out)
    decode_message(out)
    return out

# =========================
# Message broadcast & matching
# =========================
def find_adsb_match(data: dict):
    """Return (hex, aircraft) of the best fresh ADS-B match for a radio message, or (None, None)."""
    acars_flight = str(data.get("flight") or "").strip()
    acars_tail   = _norm_reg(data.get("tail"))
    acars_hex    = str(data.get("hex") or "").strip().lower()
    if not (acars_flight or acars_tail or acars_hex):
        return None, None

    now = time.time()
    best, best_score = (None, None), 0
    for hex_id, info in adsb_aircraft.items():
        if now - info.get("last_seen", 0) > ADSB_TIMEOUT:
            continue
        ac = info["data"]
        if ac.get("lat") is None or ac.get("lon") is None:
            continue

        score = 0
        if acars_hex and acars_hex == hex_id.lower():
            score = 3
        else:
            reg = _norm_reg(ac.get("r") or ac.get("reg"))
            if len(acars_tail) >= 3 and reg and (acars_tail == reg or acars_tail.lstrip("N") == reg.lstrip("N")):
                score = 2
            elif acars_flight and flights_match(acars_flight, ac.get("flight")):
                score = 1

        if score > best_score:
            best, best_score = (hex_id.lower(), ac), score
            if score == 3:
                break
    return best

async def broadcast_message(data: dict):
    global total_message_count, matched_message_count, message_seq, history_dirty
    now = time.time()

    message_seq += 1
    data["id"] = message_seq
    if not data.get("timestamp"):
        data["timestamp"] = now

    total_message_count += 1
    if data.get("freq") is not None:
        try:
            key = f"{float(data['freq']):.3f}"
            frequency_counts[key] = frequency_counts.get(key, 0) + 1
        except Exception:
            pass

    src = (data.get("source") or "").lower()
    if src == "acars":
        acars_times.append(now); _prune_times(acars_times, now)
    elif src == "vdlm2":
        vdlm2_times.append(now); _prune_times(vdlm2_times, now)

    airline_name = parse_airline(data.get("flight"))
    if airline_name:
        airline_counts[airline_name] = airline_counts.get(airline_name, 0) + 1

    # Match to ADS-B (hex / registration / flight), count distance only if position present
    try:
        hex_id, ac = find_adsb_match(data)
        if ac:
            lat, lon = float(ac["lat"]), float(ac["lon"])
            dist = calculate_distance_miles(HOME_LAT, HOME_LON, lat, lon)
            brg = bearing_deg(HOME_LAT, HOME_LON, lat, lon)
            card = bearing_to_cardinal(brg)
            distance_bins[get_distance_bin_index(dist)] += 1
            matched_message_count += 1
            recent_verified[hex_id] = now
            data["distance"] = round(dist, 1)
            data["cardinal"] = card
            data["matched_hex"] = hex_id
            note_coverage(src, lat, lon, dist, brg, data.get("flight"))

            adsb_flight = str(ac.get("flight") or "").strip()
            flight_show = (str(data.get("flight") or "").strip() or adsb_flight).upper()
            airline = parse_airline(flight_show) or parse_airline(adsb_flight) or ""
            src_show = src.upper() or "RADIO"
            await broadcast_notify({
                "text": f"{(airline + ' ') if airline else ''}{flight_show} sent {src_show} ~{int(round(dist))} mi to the {card}",
                "airline": airline,
                "flight": flight_show,
                "hex": hex_id,
                "distance": dist,
                "bearing": brg,
                "cardinal": card,
                "source": src_show,
            })
    except Exception as e:
        print(f"[MATCH] error: {e}")

    # Route: the aircraft's own report wins; otherwise the scheduled route for its callsign
    try:
        rr = extract_radio_route(data)
        if rr:
            remember_radio_route(rr, data)
        adsb_cs = None
        pos = None
        mh = data.get("matched_hex")
        if mh and adsb_aircraft.get(mh):
            adsb_cs = adsb_aircraft[mh]["data"].get("flight")
            pos = pos_of(adsb_aircraft[mh]["data"])
        elif isinstance(data.get("pos_lat"), (int, float)) and isinstance(data.get("pos_lon"), (int, float)):
            pos = (data["pos_lat"], data["pos_lon"], None)
        route = get_route(mh or data.get("hex"), data.get("tail"), data.get("flight"), adsb_cs, pos=pos)
        if route:
            data["route"] = route
    except Exception as e:
        print(f"[ROUTES] error: {e}")

    # Alerts
    msg_text = data.get("msg_text") or data.get("text") or data.get("message") or data.get("summary")
    if is_alert_message(msg_text):
        data["alert"] = True
        data["aid"] = f"{int(now * 1000)}-{message_seq}"
        data["starred"] = False
        alerts_history.append(dict(data))
        trim_alerts()
        save_alerts_history()
        try:
            queue_pushover_alert(data)
        except Exception as e:
            print(f"[PUSHOVER] error: {e}")

    # Position reported over the radio (POS reports, ADS-C) -> map
    try:
        plat, plon = data.get("pos_lat"), data.get("pos_lon")
        if isinstance(plat, (int, float)) and isinstance(plon, (int, float)) and not (plat == 0 and plon == 0):
            pdist = calculate_distance_miles(HOME_LAT, HOME_LON, plat, plon)
            key = (str(data.get("hex") or "").lower()
                   or _norm_reg(data.get("tail"))
                   or str(data.get("flight") or "").strip().upper())
            if key and pdist <= ACARS_POS_MAX_MI:
                pcard = bearing_to_cardinal(bearing_deg(HOME_LAT, HOME_LON, plat, plon))
                note_coverage(src, plat, plon, pdist, bearing_deg(HOME_LAT, HOME_LON, plat, plon), data.get("flight"))
                data["pos_key"] = key
                data["pos_distance"] = round(pdist, 1)
                data["pos_cardinal"] = pcard
                acars_positions[key] = {
                    "key": key, "lat": plat, "lon": plon, "ts": now,
                    "alt": data.get("parsed_alt_ft"),
                    "flight": data.get("flight"), "tail": data.get("tail"), "hex": data.get("hex"),
                    "adsb_hex": data.get("matched_hex"),
                    "source": src, "summary": data.get("decoded") or data.get("parsed_summary"),
                    "distance": round(pdist, 1), "cardinal": pcard,
                }
    except Exception as e:
        print(f"[POSMAP] error: {e}")

    # Long-term log for Trends (written in batches)
    try:
        ts = float(data.get("timestamp") or now)
    except (TypeError, ValueError):
        ts = now
    try:
        freq = float(data["freq"]) if data.get("freq") is not None else None
    except (TypeError, ValueError):
        freq = None
    db_buffer.append((
        ts, src or None, freq,
        str(data.get("flight") or "").strip().upper() or None,
        data.get("tail"), data.get("hex"), data.get("label"),
        data.get("msg_type"), airline_name,
        1 if data.get("distance") is not None else 0,
        data.get("distance"),
        1 if data.get("alert") else 0,
        1 if data.get("pos_key") else 0,
    ))

    try:
        log_flight_message(data)
    except Exception as e:
        print(f"[TIMELINE] error: {e}")

    # Recent history for seeding new browsers (flushed to disk periodically)
    stored_messages.append(dict(data))
    del stored_messages[:-MAX_MESSAGES]
    history_dirty = True

    await _send_all(json.dumps({"type": "message", "data": data}))
    await broadcast_status()

# =========================
# SQLite message log + Trends
# =========================
def _db_connect():
    con = sqlite3.connect(DB_PATH, timeout=10)
    con.execute("PRAGMA journal_mode=WAL")
    return con

def db_init():
    try:
        con = _db_connect()
        try:
            with con:
                con.execute("""CREATE TABLE IF NOT EXISTS messages (
                    ts REAL NOT NULL, source TEXT, freq REAL, flight TEXT, tail TEXT, hex TEXT,
                    label TEXT, msg_type TEXT, airline TEXT, verified INTEGER, distance REAL,
                    alert INTEGER, has_pos INTEGER)""")
                con.execute("CREATE INDEX IF NOT EXISTS idx_messages_ts ON messages(ts)")
        finally:
            con.close()
        print(f"[DB] Message log ready -> {DB_PATH}")
    except Exception as e:
        print(f"[DB] Init failed: {e}")

def db_write(rows):
    if not rows:
        return
    try:
        con = _db_connect()
        try:
            with con:
                con.executemany("INSERT INTO messages VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)", rows)
        finally:
            con.close()
    except Exception as e:
        print(f"[DB] Write failed ({len(rows)} rows): {e}")

def db_prune():
    try:
        con = _db_connect()
        try:
            with con:
                n = con.execute("DELETE FROM messages WHERE ts < ?", (time.time() - DB_RETENTION_DAYS * 86400,)).rowcount
        finally:
            con.close()
        if n:
            print(f"[DB] Pruned {n} rows older than {DB_RETENTION_DAYS} days")
    except Exception as e:
        print(f"[DB] Prune failed: {e}")

async def periodic_db_flush():
    last_prune = 0
    while True:
        await asyncio.sleep(DB_FLUSH_SEC)
        rows = db_buffer[:]
        del db_buffer[:len(rows)]
        await asyncio.to_thread(db_write, rows)
        if time.time() - last_prune > 6 * 3600:
            last_prune = time.time()
            await asyncio.to_thread(db_prune)

def query_trends(days: int) -> dict:
    days = max(1, min(int(days), DB_RETENTION_DAYS))
    now = time.time()
    lt = time.localtime(now)
    midnight = time.mktime((lt.tm_year, lt.tm_mon, lt.tm_mday, 0, 0, 0, 0, 0, -1))
    start = midnight - (days - 1) * 86400
    con = sqlite3.connect(DB_PATH, timeout=10)
    try:
        q = con.execute
        # Last 48 hours, hourly, by source
        hourly_rows = q("""SELECT CAST(ts / 3600 AS INTEGER) AS h, source, COUNT(*) FROM messages
                           WHERE ts >= ? GROUP BY h, source""", (now - 48 * 3600,)).fetchall()
        cur_h = int(now // 3600)
        hmap = {}
        for h, s, c in hourly_rows:
            hmap.setdefault(h, {})[s or "other"] = c
        hourly = [{"t": h * 3600, "acars": hmap.get(h, {}).get("acars", 0), "vdlm2": hmap.get(h, {}).get("vdlm2", 0)}
                  for h in range(cur_h - 47, cur_h + 1)]

        # Daily totals (local days)
        drows = q("""SELECT date(ts, 'unixepoch', 'localtime') AS d, COUNT(*), SUM(verified), SUM(has_pos), MAX(distance)
                     FROM messages WHERE ts >= ? GROUP BY d""", (start,)).fetchall()
        dmap = {r[0]: r for r in drows}
        daily = []
        for i in range(days):
            d = time.strftime("%Y-%m-%d", time.localtime(start + i * 86400 + 7200))
            r = dmap.get(d)
            daily.append({"date": d, "total": r[1] if r else 0, "verified": (r[2] or 0) if r else 0,
                          "positions": (r[3] or 0) if r else 0, "max_dist": r[4] if r else None})
        ndays = max(1, len(drows))

        # Average by hour of day
        hod = [0.0] * 24
        for hr, c in q("""SELECT CAST(strftime('%H', ts, 'unixepoch', 'localtime') AS INTEGER) AS hr, COUNT(*)
                          FROM messages WHERE ts >= ? GROUP BY hr""", (start,)).fetchall():
            if hr is not None and 0 <= hr < 24:
                hod[hr] = round(c / ndays, 1)

        types = q("""SELECT COALESCE(msg_type, 'Other'), COUNT(*) FROM messages WHERE ts >= ?
                     GROUP BY 1 ORDER BY 2 DESC LIMIT 12""", (start,)).fetchall()
        airlines = q("""SELECT airline, COUNT(*) FROM messages WHERE ts >= ? AND airline IS NOT NULL
                        GROUP BY airline ORDER BY 2 DESC LIMIT 10""", (start,)).fetchall()
        far = q("""SELECT flight, tail, distance, ts, source FROM messages WHERE ts >= ? AND distance IS NOT NULL
                   ORDER BY distance DESC LIMIT 1""", (start,)).fetchone()
        oldest = q("SELECT MIN(ts) FROM messages").fetchone()[0]
    finally:
        con.close()

    total = sum(d["total"] for d in daily)
    return {
        "ok": True, "days": days, "generated": now, "oldest": oldest, "ndays": ndays,
        "total": total,
        "verified": sum(d["verified"] for d in daily),
        "positions": sum(d["positions"] for d in daily),
        "hourly": hourly, "daily": daily, "hod": hod,
        "types": types, "airlines": airlines,
        "farthest": ({"flight": far[0], "tail": far[1], "distance": far[2], "ts": far[3], "source": far[4]} if far else None),
    }

def acars_positions_snapshot() -> bytes:
    now = time.time()
    for k in [k for k, p in acars_positions.items() if now - p["ts"] > ACARS_POS_MAX_AGE]:
        acars_positions.pop(k, None)
    out = []
    for p in list(acars_positions.values()):
        q = dict(p)
        try:
            q["route"] = get_route(p.get("hex"), p.get("tail"), p.get("flight"), pos=(p["lat"], p["lon"], None))
        except Exception:
            q["route"] = None
        out.append(q)
    return json.dumps({"now": now, "positions": out}).encode()

# =========================
# Readers
# =========================
async def read_json_lines(host: str, port: int, normalizer, name: str):
    while True:
        try:
            reader, writer = await asyncio.open_connection(host, port)
            stream_status[name] = True
            await broadcast_status()
            print(f"[CONNECT] {name} connected {host}:{port}")
            try:
                while True:
                    line = await reader.readline()
                    if not line:
                        break
                    s = line.decode(errors="ignore").strip()
                    if not s:
                        continue
                    # Handle back-to-back objects on one line too.
                    for chunk in s.replace("}{", "}\n{").splitlines():
                        try:
                            obj = json.loads(chunk)
                        except json.JSONDecodeError:
                            continue
                        try:
                            data = normalizer(obj)
                            if data:
                                await broadcast_message(data)
                        except Exception as e:
                            # A single bad message must never drop the connection.
                            print(f"[READER] {name} message error -> {e}")
            finally:
                writer.close()
        except Exception as e:
            print(f"[READER] {name} error -> {e}")
        if stream_status.get(name, False):
            stream_status[name] = False
            await broadcast_status()
        await asyncio.sleep(2.0)

# =========================
# HTTP server
# =========================
class Handler(BaseHTTPRequestHandler):
    def log_request(self, code="-", size="-"):
        # Quiet: the browser polls every few seconds. Still log errors.
        if str(getattr(code, "value", code)).startswith(("4", "5")):
            super().log_request(code, size)

    def _send(self, status, ctype, body, extra=None):
        self.send_response(status)
        self.send_header("Content-type", ctype)
        self.send_header("Content-length", str(len(body)))
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        path = urlsplit(self.path).path

        if path in ("/", "/index.html"):
            content = (HTML_PAGE
                       .replace("%%HOME_LAT%%", str(HOME_LAT))
                       .replace("%%HOME_LON%%", str(HOME_LON))
                       .replace("%%WS_PORT%%", str(WS_PORT))
                       ).encode("utf-8")
            self._send(200, "text/html; charset=utf-8", content, {"Cache-Control": "no-store"})
            return

        if path == "/aircraft.json":
            if not stream_status.get("adsb"):
                self._send(502, "text/plain", b"ADS-B source unavailable")
                return
            self._send(200, "application/json", adsb_snapshot, {"Cache-Control": "no-store"})
            return

        if path == "/acars_positions.json":
            try:
                body = acars_positions_snapshot()
            except Exception:
                body = b'{"positions": []}'
            self._send(200, "application/json", body, {"Cache-Control": "no-store"})
            return

        if path == "/api/track":
            try:
                qs = parse_qs(urlsplit(self.path).query)
                body = json.dumps(track_payload((qs.get("hex") or [None])[0], (qs.get("key") or [None])[0])).encode()
            except Exception as e:
                print(f"[TRACK] failed: {e}")
                body = b'{"trail": [], "route": null}'
            self._send(200, "application/json", body, {"Cache-Control": "no-store"})
            return

        if path == "/api/coverage":
            self._send(200, "application/json", coverage_payload(), {"Cache-Control": "no-store"})
            return

        if path == "/api/metar":
            body = json.dumps({"station": METAR_STATION, "metar": metar_latest, "error": metar_error}).encode()
            self._send(200, "application/json", body, {"Cache-Control": "no-store"})
            return

        if path == "/api/flight":
            try:
                qs = parse_qs(urlsplit(self.path).query)
                g = lambda k: ((qs.get(k) or [None])[0] or None)
                body = json.dumps(flight_payload(g("flight"), g("tail"), g("hex"))).encode()
            except Exception as e:
                print(f"[TIMELINE] query failed: {e}")
                body = json.dumps({"error": str(e), "messages": []}).encode()
            self._send(200, "application/json", body, {"Cache-Control": "no-store"})
            return

        if path == "/api/trails":
            try:
                body = trails_payload()
            except Exception:
                body = b'{"trails": {}}'
            self._send(200, "application/json", body, {"Cache-Control": "no-store"})
            return

        if path == "/api/trends":
            try:
                qs = parse_qs(urlsplit(self.path).query)
                days = int((qs.get("days") or ["7"])[0])
                body = json.dumps(query_trends(days)).encode()
            except Exception as e:
                print(f"[TRENDS] query failed: {e}")
                body = json.dumps({"ok": False, "error": str(e)}).encode()
            self._send(200, "application/json", body, {"Cache-Control": "no-store"})
            return

        if path.startswith("/static/"):
            try:
                safe_rel = os.path.normpath(unquote(path.lstrip("/")))
                fs_path  = os.path.join(BASE_DIR, safe_rel)
                static_root = os.path.join(BASE_DIR, "static")
                if os.path.commonpath([fs_path, static_root]) != static_root:
                    self._send(403, "text/plain", b"Forbidden")
                    return
                if not os.path.isfile(fs_path):
                    self._send(404, "text/plain", b"Not found")
                    return
                ctype, _ = mimetypes.guess_type(fs_path)
                with open(fs_path, "rb") as f:
                    data = f.read()
                self._send(200, ctype or "application/octet-stream", data, {"Cache-Control": "max-age=3600"})
            except Exception as e:
                print(f"[STATIC] Error: {e}")
                self._send(500, "text/plain", b"Error")
            return

        self._send(404, "text/plain", b"Not found")

# =========================
# HTML UI
# =========================
HTML_PAGE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8"/>
<meta name="viewport" content="width=device-width, initial-scale=1"/>
<title>Live Aviation Dashboard</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800&family=JetBrains+Mono:wght@400;500;700&display=swap" rel="stylesheet">
<link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css" crossorigin=""/>
<style>
:root {
    --bg: #05070c;
    --panel: rgba(13, 19, 30, 0.84);
    --panel-hi: rgba(19, 27, 41, 0.94);
    --border: rgba(140, 170, 210, 0.12);
    --border-hi: rgba(140, 170, 210, 0.28);
    --text: #e8eef6;
    --muted: #8696ab;
    --dim: #526176;
    --acars: #fbbf24;
    --vdlm2: #a78bfa;
    --adsb: #38bdf8;
    --ok: #22e584;
    --alert: #f43f5e;
    --mono: "JetBrains Mono", ui-monospace, Consolas, monospace;
    --sans: Inter, ui-sans-serif, system-ui, "Segoe UI", Roboto, sans-serif;
    --radius: 14px;
}

* { box-sizing: border-box; }
html, body { margin: 0; }

body {
    font-family: var(--sans);
    color: var(--text);
    background:
        radial-gradient(1100px 600px at 0% -10%, rgba(251, 191, 36, 0.07), transparent 60%),
        radial-gradient(900px 600px at 105% 0%, rgba(167, 139, 250, 0.09), transparent 60%),
        var(--bg);
    background-attachment: fixed;
    min-height: 100vh;
    -webkit-font-smoothing: antialiased;
}

body::before {
    content: "";
    position: fixed;
    inset: 0;
    pointer-events: none;
    background-image:
        linear-gradient(rgba(255, 255, 255, 0.02) 1px, transparent 1px),
        linear-gradient(90deg, rgba(255, 255, 255, 0.02) 1px, transparent 1px);
    background-size: 44px 44px;
    -webkit-mask-image: radial-gradient(ellipse at 50% 20%, black 20%, transparent 75%);
    mask-image: radial-gradient(ellipse at 50% 20%, black 20%, transparent 75%);
}

a { color: var(--adsb); text-decoration: none; }
.mono { font-family: var(--mono); }
.na { color: var(--dim); }
.wrap { max-width: 1600px; margin: 0 auto; padding: 0 16px; position: relative; }

button {
    font: inherit;
    font-size: 12.5px;
    font-weight: 600;
    color: var(--muted);
    background: rgba(255, 255, 255, 0.03);
    border: 1px solid var(--border);
    border-radius: 10px;
    padding: 6px 11px;
    cursor: pointer;
    transition: color 0.15s, border-color 0.15s, background 0.15s;
}
button:hover { color: var(--text); border-color: var(--border-hi); }
button.on { color: var(--text); background: rgba(255, 255, 255, 0.08); border-color: var(--border-hi); }

/* ---------- Header ---------- */
header.top {
    position: sticky;
    top: 0;
    z-index: 1000;
    background: rgba(5, 7, 12, 0.78);
    backdrop-filter: blur(14px);
    -webkit-backdrop-filter: blur(14px);
    border-bottom: 1px solid var(--border);
}

.head { display: flex; align-items: center; gap: 16px; flex-wrap: wrap; padding: 12px 0; }
.brand { display: flex; align-items: center; gap: 12px; }
.wx { display: flex; align-items: stretch; gap: 0; margin-right: auto; padding: 5px 4px; border-radius: 12px; border: 1px solid var(--border); background: var(--panel); min-height: 42px; }
.wx[hidden] { display: none; }
.wx > div { padding: 0 10px; display: flex; flex-direction: column; justify-content: center; border-left: 1px solid rgba(255, 255, 255, 0.06); white-space: nowrap; }
.wx > div:first-child { border-left: 0; }
.wx .t { font-family: var(--mono); font-size: 14px; font-weight: 700; display: flex; align-items: center; gap: 5px; }
.wx .t small { font-size: 11px; color: var(--muted); font-weight: 500; }
.wx .l { font-size: 9.5px; letter-spacing: 0.14em; color: var(--muted); text-transform: uppercase; margin-top: 1px; }
.wx .cat { font: 800 11px var(--mono); letter-spacing: 0.06em; padding: 2px 6px; border-radius: 5px; color: #06130b; background: var(--cat, #64748b); }
.wx .stn { font-family: var(--mono); font-weight: 700; font-size: 13px; }
.wx .arrow { width: 13px; height: 13px; flex: 0 0 13px; }
.wx .arrow path { fill: var(--adsb); }
.wx.stale .t { color: var(--muted); }
@media (max-width: 1300px) { .wx .w-sky { display: none; } }
@media (max-width: 1150px) { .wx .w-vis { display: none; } }
@media (max-width: 1000px) and (min-width: 641px) { .head .clock { display: none; } }
.wx .w-sky .t, .wx .w-sky .l { max-width: 160px; overflow: hidden; text-overflow: ellipsis; display: block; }
@media (max-width: 1520px) and (min-width: 641px) {
    /* make room for the weather strip: status lights become dots (names on hover) */
    .lights .light { font-size: 0; gap: 0; padding: 8px; letter-spacing: 0; }
}
@media (max-width: 640px) {
    .wx { order: 3; width: 100%; margin-right: 0; flex-wrap: wrap; row-gap: 8px; padding: 7px 4px; }
    .wx > div { flex: 1 1 30%; min-width: 0; border-left: 0; padding: 0 8px; }
    .wx .w-baro, .wx .w-vis, .wx .w-sky { display: flex; }
    .wx .w-sky .t, .wx .w-sky .l { max-width: 100%; }
}

.logo {
    width: 42px;
    height: 42px;
    border-radius: 12px;
    display: grid;
    place-items: center;
    background: linear-gradient(135deg, rgba(251, 191, 36, 0.22), rgba(167, 139, 250, 0.22));
    border: 1px solid var(--border-hi);
    box-shadow: 0 0 24px rgba(251, 191, 36, 0.15);
}
.logo svg { width: 24px; height: 24px; }

h1 { margin: 0; font-size: 18px; font-weight: 800; letter-spacing: 0.01em; }
.sub { color: var(--muted); font-size: 11.5px; letter-spacing: 0.12em; text-transform: uppercase; margin-top: 2px; }
.sub b { font-weight: 700; }

.lights { display: flex; gap: 6px; flex-wrap: wrap; }

.light {
    display: inline-flex;
    align-items: center;
    gap: 7px;
    padding: 6px 11px;
    border-radius: 999px;
    border: 1px solid var(--border);
    background: var(--panel);
    font-family: var(--mono);
    font-size: 11px;
    font-weight: 700;
    letter-spacing: 0.08em;
    color: var(--dim);
}
.light i { width: 8px; height: 8px; border-radius: 50%; background: var(--alert); box-shadow: 0 0 8px var(--alert); }
.light.up { color: var(--text); }
.light.up i { background: var(--c, var(--ok)); box-shadow: 0 0 0 0 var(--c, var(--ok)); animation: ping 2.2s infinite; }

@keyframes ping {
    0% { box-shadow: 0 0 0 0 color-mix(in srgb, var(--c, #22e584) 70%, transparent); }
    70% { box-shadow: 0 0 0 7px transparent; }
    100% { box-shadow: 0 0 0 0 transparent; }
}

.clock { display: flex; gap: 14px; padding: 5px 14px; border-radius: 12px; border: 1px solid var(--border); background: var(--panel); }
.clock div { text-align: right; }
.clock .t { font-family: var(--mono); font-size: 15px; font-weight: 700; }
.clock .l { font-size: 9.5px; letter-spacing: 0.14em; color: var(--muted); text-transform: uppercase; }

/* ---------- Watch banner ---------- */
.watch {
    display: flex;
    align-items: center;
    gap: 12px;
    flex-wrap: wrap;
    margin-top: 14px;
    padding: 10px 14px;
    border-radius: var(--radius);
    background: linear-gradient(90deg, rgba(34, 229, 132, 0.14), rgba(34, 229, 132, 0.04));
    border: 1px solid rgba(34, 229, 132, 0.4);
    box-shadow: 0 0 30px rgba(34, 229, 132, 0.12);
}
.watch[hidden] { display: none; }
.watch .w-title { font-size: 11px; font-weight: 800; letter-spacing: 0.16em; color: var(--ok); display: flex; align-items: center; gap: 8px; }
.watch .w-title i { width: 9px; height: 9px; border-radius: 50%; background: var(--ok); animation: ping 1.6s infinite; --c: #22e584; }
.w-items { display: flex; gap: 8px; flex-wrap: wrap; }
.w-item {
    display: inline-flex;
    gap: 8px;
    align-items: center;
    padding: 5px 12px;
    border-radius: 999px;
    background: rgba(0, 0, 0, 0.25);
    border: 1px solid rgba(34, 229, 132, 0.3);
    color: #c9fbe3;
    font-size: 12.5px;
}
.w-item:hover { border-color: var(--ok); text-decoration: none; }
.w-item b { font-family: var(--mono); color: #fff; }
.w-item.fresh { animation: glowIn 2.4s ease; }
@keyframes glowIn { 0%, 40% { box-shadow: 0 0 0 3px rgba(34, 229, 132, 0.5), 0 0 24px rgba(34, 229, 132, 0.5); } 100% { box-shadow: none; } }

/* ---------- KPIs ---------- */
.kpis { display: grid; grid-template-columns: repeat(6, minmax(0, 1fr)); gap: 12px; margin: 14px 0; }
.kpis[hidden] { display: none; }

.kpi {
    position: relative;
    overflow: hidden;
    background: var(--panel);
    border: 1px solid var(--border);
    border-radius: var(--radius);
    padding: 13px 15px;
    min-width: 0;
}
.kpi::before { content: ""; position: absolute; inset: 0 auto 0 0; width: 3px; background: var(--c); box-shadow: 0 0 14px var(--c); }
.kpi .k { font-size: 10.5px; font-weight: 700; color: var(--muted); letter-spacing: 0.12em; text-transform: uppercase; }
.kpi .v { font-family: var(--mono); font-size: 28px; font-weight: 700; margin-top: 3px; color: var(--c); line-height: 1.1; }
.kpi .v small { font-size: 13px; color: var(--muted); font-weight: 500; }
.kpi .h { font-size: 11.5px; color: var(--dim); margin-top: 3px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.kpi .spark { position: absolute; right: 10px; top: 12px; width: 44%; height: 34px; opacity: 0.9; }
.kpi .spark svg { width: 100%; height: 100%; display: block; }
.meter { height: 4px; border-radius: 999px; background: rgba(255, 255, 255, 0.07); margin-top: 7px; overflow: hidden; }
.meter div { height: 100%; background: var(--c); border-radius: 999px; transition: width 0.6s ease; }
.bump { animation: bump 0.5s ease; }
@keyframes bump { 30% { transform: scale(1.12); text-shadow: 0 0 14px currentColor; } }

/* ---------- Tabs ---------- */
.tabs {
    position: sticky;
    top: 67px;
    z-index: 900;
    display: flex;
    gap: 6px;
    padding: 8px;
    margin-bottom: 14px;
    border-radius: var(--radius);
    background: rgba(10, 15, 24, 0.88);
    backdrop-filter: blur(12px);
    -webkit-backdrop-filter: blur(12px);
    border: 1px solid var(--border);
    overflow-x: auto;
}
.tab { display: inline-flex; align-items: center; gap: 8px; padding: 8px 14px; font-size: 13px; white-space: nowrap; }
.tab svg { width: 16px; height: 16px; }
.tab.on { background: rgba(255, 255, 255, 0.09); }
.badge {
    min-width: 20px;
    padding: 1px 7px;
    border-radius: 999px;
    font-family: var(--mono);
    font-size: 11px;
    background: rgba(255, 255, 255, 0.08);
    color: var(--muted);
}
.tab[data-tab="nearby"].hot { color: var(--ok); border-color: rgba(34, 229, 132, 0.5); animation: tabPulse 2s infinite; --c: #22e584; }
.tab[data-tab="nearby"].hot .badge { background: rgba(34, 229, 132, 0.2); color: var(--ok); }
.tab[data-tab="alerts"].hot { color: var(--alert); border-color: rgba(244, 63, 94, 0.55); animation: tabPulse 1.6s infinite; --c: #f43f5e; }
.tab[data-tab="alerts"].hot .badge { background: rgba(244, 63, 94, 0.22); color: #fecdd3; }
@keyframes tabPulse {
    0%, 100% { box-shadow: 0 0 0 0 transparent; }
    50% { box-shadow: 0 0 16px color-mix(in srgb, var(--c) 45%, transparent); }
}

.view[hidden] { display: none !important; }

/* ---------- Panels ---------- */
.panel {
    background: var(--panel);
    border: 1px solid var(--border);
    border-radius: var(--radius);
    padding: 14px 16px;
    min-width: 0;
}
.panel-title {
    display: flex;
    align-items: center;
    justify-content: space-between;
    gap: 10px;
    font-size: 11.5px;
    font-weight: 700;
    letter-spacing: 0.12em;
    text-transform: uppercase;
    color: var(--muted);
    margin-bottom: 12px;
}
.panel-title .r { font-family: var(--mono); font-weight: 500; letter-spacing: 0; text-transform: none; color: var(--dim); }

.live-grid { display: grid; grid-template-columns: minmax(0, 1.45fr) minmax(0, 1fr) minmax(0, 1fr); gap: 14px; align-items: start; }
.col { display: grid; gap: 14px; min-width: 0; }

/* ---------- Feed ---------- */
.feed-tools { display: flex; gap: 6px; flex-wrap: wrap; align-items: center; margin-bottom: 12px; }
.feed-tools .grow { flex: 1; }
.fchip { border-radius: 999px; padding: 5px 11px; font-size: 12px; }
.fchip.on[data-filter="acars"] { color: var(--acars); border-color: color-mix(in srgb, var(--acars) 50%, transparent); background: color-mix(in srgb, var(--acars) 12%, transparent); }
.fchip.on[data-filter="vdlm2"] { color: var(--vdlm2); border-color: color-mix(in srgb, var(--vdlm2) 50%, transparent); background: color-mix(in srgb, var(--vdlm2) 12%, transparent); }
.fchip.on[data-filter="verified"] { color: var(--ok); border-color: color-mix(in srgb, var(--ok) 50%, transparent); background: color-mix(in srgb, var(--ok) 12%, transparent); }
.fchip.on[data-filter="alerts"] { color: var(--alert); border-color: color-mix(in srgb, var(--alert) 50%, transparent); background: color-mix(in srgb, var(--alert) 12%, transparent); }

input[type="search"] {
    font: inherit;
    font-size: 12.5px;
    color: var(--text);
    background: rgba(255, 255, 255, 0.04);
    border: 1px solid var(--border);
    border-radius: 10px;
    padding: 6px 11px;
    width: 190px;
    max-width: 100%;
    outline: none;
}
input[type="search"]:focus { border-color: var(--border-hi); }

#pause.on { color: var(--acars); border-color: color-mix(in srgb, var(--acars) 50%, transparent); }

.feed { display: grid; gap: 10px; }

.msg {
    --c: var(--muted);
    position: relative;
    background: var(--panel-hi);
    border: 1px solid var(--border);
    border-left: 3px solid var(--c);
    border-radius: 12px;
    padding: 11px 13px;
    min-width: 0;
}
.msg.s-acars { --c: var(--acars); }
.msg.s-vdlm2 { --c: var(--vdlm2); }
.msg.verified { box-shadow: inset 0 0 0 1px rgba(34, 229, 132, 0.18); }
.msg.alert { border-color: rgba(244, 63, 94, 0.5); border-left-color: var(--alert); box-shadow: 0 0 0 1px rgba(244, 63, 94, 0.2), 0 0 20px rgba(244, 63, 94, 0.18); }
.msg.enter { animation: enter 0.5s ease; }
@keyframes enter { from { opacity: 0; transform: translateY(-8px); background: rgba(255, 255, 255, 0.08); } to { opacity: 1; transform: none; } }

.m-head { display: flex; align-items: center; gap: 10px; }
.m-id { flex: 1; min-width: 0; }
.m-flight { font-family: var(--mono); font-weight: 700; font-size: 15px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.m-tail { color: var(--muted); font-weight: 500; font-size: 12.5px; margin-left: 6px; }
.m-sub { font-size: 12px; color: var(--muted); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.m-meta { text-align: right; flex: 0 0 auto; }
.src-badge {
    font-family: var(--mono);
    font-size: 10px;
    font-weight: 800;
    letter-spacing: 0.1em;
    padding: 2px 7px;
    border-radius: 6px;
    color: var(--c);
    background: color-mix(in srgb, var(--c) 14%, transparent);
}
.m-time { font-family: var(--mono); font-size: 11px; color: var(--dim); margin-top: 4px; }

.m-text {
    margin: 9px 0 0;
    font-family: var(--mono);
    font-size: 12px;
    line-height: 1.55;
    color: #cfd8e4;
    white-space: pre-wrap;
    word-break: break-word;
    background: rgba(0, 0, 0, 0.22);
    border-radius: 8px;
    padding: 8px 10px;
    max-height: 9.5em;
    overflow: hidden;
    cursor: pointer;
}
.msg.open .m-text { max-height: none; }
mark { background: rgba(244, 63, 94, 0.3); color: #fff; border-radius: 3px; padding: 0 2px; }

.chips { display: flex; gap: 6px; flex-wrap: wrap; margin-top: 9px; }
.chip {
    display: inline-flex;
    gap: 5px;
    font-size: 11px;
    padding: 3px 8px;
    border-radius: 999px;
    border: 1px solid var(--border);
    color: var(--muted);
    background: rgba(0, 0, 0, 0.15);
    font-family: var(--mono);
}
.chip b { color: var(--dim); font-weight: 600; font-family: var(--sans); }
.chip.ok { color: var(--ok); border-color: rgba(34, 229, 132, 0.4); background: rgba(34, 229, 132, 0.08); cursor: pointer; }
.chip.ok:hover { background: rgba(34, 229, 132, 0.16); }

.pending { display: none; width: 100%; margin-bottom: 10px; color: var(--acars); border-color: color-mix(in srgb, var(--acars) 45%, transparent); }
.pending.show { display: block; }

.empty { text-align: center; color: var(--dim); padding: 36px 12px; border: 1px dashed var(--border); border-radius: 12px; font-size: 13px; }

/* Avatar */
.av {
    position: relative;
    width: 36px;
    height: 36px;
    flex: 0 0 36px;
    border-radius: 10px;
    display: grid;
    place-items: center;
    font-family: var(--mono);
    font-weight: 700;
    font-size: 12px;
    color: hsl(var(--h) 80% 80%);
    background: linear-gradient(135deg, hsl(var(--h) 55% 28% / 0.6), hsl(var(--h) 55% 16% / 0.6));
    border: 1px solid hsl(var(--h) 55% 50% / 0.3);
    overflow: hidden;
}
.av img { position: absolute; inset: 0; width: 100%; height: 100%; object-fit: contain; background: #0c111a; padding: 3px; }

/* ---------- Stat panels ---------- */
.freq-row { display: grid; grid-template-columns: 84px minmax(0, 1fr) 54px; gap: 10px; align-items: center; padding: 4px 0; font-size: 12px; }
.freq-row .f { font-family: var(--mono); color: var(--text); }
.freq-row .n { font-family: var(--mono); text-align: right; color: var(--muted); }
.track { height: 8px; border-radius: 999px; background: rgba(255, 255, 255, 0.05); overflow: hidden; }
.track div { height: 100%; border-radius: 999px; background: linear-gradient(90deg, var(--acars), color-mix(in srgb, var(--acars) 45%, transparent)); transition: width 0.6s ease; }
.freq-row.vdl .track div { background: linear-gradient(90deg, var(--vdlm2), color-mix(in srgb, var(--vdlm2) 45%, transparent)); }

.dist { display: grid; grid-template-columns: repeat(5, 1fr); gap: 8px; align-items: end; height: 130px; }
.dist .b { display: flex; flex-direction: column; justify-content: flex-end; align-items: center; height: 100%; gap: 5px; }
.dist .bar { width: 100%; border-radius: 7px 7px 3px 3px; background: linear-gradient(180deg, var(--ok), rgba(34, 229, 132, 0.25)); box-shadow: 0 0 14px rgba(34, 229, 132, 0.2); transition: height 0.6s ease; min-height: 3px; }
.dist .c { font-family: var(--mono); font-size: 11.5px; font-weight: 700; }
.dist-labels { display: grid; grid-template-columns: repeat(5, 1fr); gap: 8px; margin-top: 6px; text-align: center; font-family: var(--mono); font-size: 10.5px; color: var(--dim); }

.al-row { display: grid; grid-template-columns: 18px 36px minmax(0, 1fr) 56px; gap: 10px; align-items: center; padding: 5px 0; font-size: 13px; border-radius: 8px; }
.al-row .rk { font-family: var(--mono); color: var(--dim); font-size: 11px; text-align: right; }
.al-row .nm { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.al-row .nm .track { margin-top: 4px; height: 4px; }
.al-row .nm .track div { background: linear-gradient(90deg, var(--adsb), rgba(56, 189, 248, 0.35)); }
.al-row .ct { font-family: var(--mono); font-weight: 700; text-align: right; }
.al-row.flash { animation: rowFlash 1.3s ease; }
@keyframes rowFlash { 0% { background: rgba(34, 229, 132, 0.2); } 100% { background: transparent; } }

/* ADS-B list */
.ac-list { display: grid; gap: 4px; max-height: 760px; overflow-y: auto; margin-right: -6px; padding-right: 6px; }
.ac-row {
    display: grid;
    grid-template-columns: 36px minmax(0, 1fr) auto;
    gap: 10px;
    align-items: center;
    padding: 7px 9px;
    border-radius: 10px;
    border: 1px solid transparent;
    background: rgba(255, 255, 255, 0.02);
    cursor: pointer;
    transition: background 0.15s, border-color 0.15s;
}
.ac-row:hover { background: rgba(255, 255, 255, 0.05); border-color: var(--border); }
.ac-row.ver { border-color: rgba(34, 229, 132, 0.35); background: rgba(34, 229, 132, 0.06); }
.ac-row .id { font-family: var(--mono); font-weight: 700; font-size: 13px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.ac-row .id .t { color: var(--dim); font-weight: 500; font-size: 11px; margin-left: 4px; }
.ac-row .meta { font-family: var(--mono); font-size: 11px; color: var(--muted); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.ac-row .dd { text-align: right; font-family: var(--mono); font-size: 12px; font-weight: 600; }
.ac-row .dd small { display: block; color: var(--dim); font-size: 10.5px; font-weight: 500; }
.up { color: var(--ok); }
.down { color: var(--adsb); }

/* ---------- Map ---------- */
.map-wrap { position: relative; border-radius: var(--radius); overflow: hidden; border: 1px solid var(--border); }
#map { height: calc(100vh - 290px); min-height: 460px; background: #070b12; }
.leaflet-container { font-family: var(--sans); background: #070b12; }
.dark-tiles { filter: invert(1) hue-rotate(200deg) brightness(0.72) contrast(0.95) saturate(0.35); }
.leaflet-popup-content-wrapper, .leaflet-popup-tip { background: rgba(10, 15, 24, 0.97); color: var(--text); border: 1px solid var(--border-hi); box-shadow: 0 12px 40px rgba(0, 0, 0, 0.6); }
.leaflet-popup-content-wrapper { border-radius: 12px; }
.leaflet-popup-content { margin: 11px 13px; font-size: 12.5px; line-height: 1.55; min-width: 190px; }
.leaflet-container a.leaflet-popup-close-button { color: var(--muted); }
.leaflet-bar a { background: rgba(13, 19, 30, 0.95); color: var(--text); border-color: var(--border); }
.leaflet-bar a:hover { background: rgba(28, 38, 56, 0.95); }
.leaflet-control-attribution { background: rgba(5, 7, 12, 0.7) !important; color: var(--dim) !important; }
.leaflet-control-attribution a { color: var(--muted) !important; }
.leaflet-tooltip { background: rgba(10, 15, 24, 0.95); color: var(--text); border: 1px solid var(--border-hi); }

.pl { position: relative; width: 100%; height: 100%; color: var(--c); }
.pl svg { width: 100%; height: 100%; fill: var(--c); filter: drop-shadow(0 0 3px rgba(0, 0, 0, 0.9)); transition: transform 0.6s ease; }
.pl.ver svg { fill: #22e584; filter: drop-shadow(0 0 5px #22e584) drop-shadow(0 0 12px rgba(34, 229, 132, 0.8)); }
.pl.trk svg { fill: #fff; filter: drop-shadow(0 0 5px #22e584) drop-shadow(0 0 14px #22e584); }
.pl-lbl {
    position: absolute;
    left: calc(100% + 3px);
    top: 50%;
    transform: translateY(-50%);
    font-family: var(--mono);
    font-size: 10.5px;
    font-weight: 700;
    color: #e8eef6;
    white-space: nowrap;
    text-shadow: 0 0 3px #000, 0 0 6px #000;
    pointer-events: none;
}
.ring-lbl { font-family: var(--mono); font-size: 10px; color: rgba(34, 229, 132, 0.75); white-space: nowrap; text-shadow: 0 0 4px #000; }

/* Emergencies */
.emg-banner { display: flex; align-items: center; gap: 12px; flex-wrap: wrap; margin-top: 14px; padding: 10px 14px; border-radius: var(--radius); background: linear-gradient(90deg, rgba(239, 68, 68, 0.28), rgba(239, 68, 68, 0.08)); border: 1px solid rgba(239, 68, 68, 0.75); box-shadow: 0 0 30px rgba(239, 68, 68, 0.25); animation: emgGlow 1.6s ease-in-out infinite; }
.emg-banner[hidden] { display: none; }
.emg-banner .e-title { font-size: 11px; font-weight: 800; letter-spacing: 0.16em; color: #fecaca; }
.emg-banner .e-item { display: inline-flex; gap: 8px; align-items: baseline; padding: 4px 10px; border-radius: 9px; background: rgba(0, 0, 0, 0.25); border: 1px solid rgba(239, 68, 68, 0.5); cursor: pointer; color: #fee2e2; font-size: 13px; }
.emg-banner .e-item b { font-family: var(--mono); font-size: 14px; color: #fff; }
.emg-banner .e-item .sq { font-family: var(--mono); font-weight: 800; color: #fca5a5; }
.emg-banner .e-item.cleared { opacity: 0.55; }
@keyframes emgGlow { 50% { box-shadow: 0 0 44px rgba(239, 68, 68, 0.45); } }
.pl.emg svg { fill: #ef4444; filter: drop-shadow(0 0 6px #ef4444) drop-shadow(0 0 14px rgba(239, 68, 68, 0.9)); }
.pl.emg svg .hs { stroke: #ef4444; }
.pl.emg::before { content: ""; position: absolute; inset: -9px; border-radius: 50%; border: 2px solid #ef4444; animation: emgRing 1.2s ease-out infinite; }
@keyframes emgRing { from { transform: scale(0.6); opacity: 1; } to { transform: scale(1.6); opacity: 0; } }
.sq-tag { display: inline-block; margin-left: 6px; padding: 0 5px; border-radius: 5px; font: 800 9.5px var(--mono); color: #fff; background: #dc2626; vertical-align: 1px; }
.pop-emg { margin: 4px 0 6px; padding: 5px 8px; border-radius: 7px; background: rgba(239, 68, 68, 0.18); border: 1px solid rgba(239, 68, 68, 0.6); color: #fecaca; font-weight: 700; font-size: 12.5px; }
.lg-cov { display: inline-block; width: 14px; height: 10px; margin-right: 8px; border: 2px solid var(--c); background: color-mix(in srgb, var(--c) 18%, transparent); border-radius: 2px; vertical-align: middle; }
.cov-legend[hidden] { display: none; }

/* Helicopters */
.pl svg .hs { fill: none; stroke: var(--c); }
.pl.ver svg .hs { stroke: #22e584; }
.pl.trk svg .hs { stroke: #fff; }
.pl svg .disk { opacity: 0.35; stroke-width: 1; }
.pl svg .blades { stroke-width: 1.7; stroke-linecap: round; transform-origin: 12px 9.5px; animation: rotor 0.7s linear infinite; }
@keyframes rotor { to { transform: rotate(360deg); } }
@media (prefers-reduced-motion: reduce) { .pl svg .blades { animation: none; } }
.heli-tag {
    display: inline-block;
    margin-left: 6px;
    padding: 0 5px;
    border-radius: 5px;
    font: 700 9.5px var(--mono);
    letter-spacing: 0.04em;
    vertical-align: 1px;
    color: #fda4af;
    border: 1px solid rgba(253, 164, 175, 0.45);
    background: rgba(253, 164, 175, 0.08);
}
.av.heli { background: rgba(253, 164, 175, 0.12); border-color: rgba(253, 164, 175, 0.35); }
.av.heli svg { width: 70%; height: 70%; fill: #fda4af; }
.av.heli svg .hs { fill: none; stroke: #fda4af; }
.lg-heli { display: inline-block; width: 14px; height: 14px; margin-right: 8px; vertical-align: middle; }
.lg-heli svg { width: 100%; height: 100%; fill: #cbd5e1; }
.lg-heli svg .hs { fill: none; stroke: #cbd5e1; }

.map-ctl { position: absolute; top: 12px; right: 12px; z-index: 500; display: flex; gap: 6px; }
.map-ctl button { background: rgba(10, 15, 24, 0.92); }
.map-legend {
    position: absolute;
    left: 12px;
    bottom: 22px;
    z-index: 500;
    display: grid;
    gap: 5px;
    padding: 10px 12px;
    border-radius: 12px;
    background: rgba(10, 15, 24, 0.9);
    border: 1px solid var(--border);
    font-size: 11.5px;
    color: var(--muted);
}
.map-legend i { display: inline-block; width: 9px; height: 9px; border-radius: 50%; margin-right: 7px; vertical-align: middle; }
.map-legend .ttl { font-family: var(--mono); color: var(--text); font-weight: 700; margin-bottom: 2px; }

.pop-id { font-family: var(--mono); font-weight: 800; font-size: 14px; }
.pop-sub { color: var(--muted); font-size: 11.5px; margin-bottom: 6px; }
.pop-row { display: flex; justify-content: space-between; gap: 14px; }
.pop-row span:first-child { color: var(--dim); }
.pop-row span:last-child { font-family: var(--mono); }
.pop-ver { margin-top: 6px; color: var(--ok); font-weight: 700; font-size: 12px; }

/* ---------- Nearby ---------- */
.near-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(300px, 1fr)); gap: 12px; }
.near {
    display: flex;
    gap: 14px;
    align-items: center;
    padding: 14px;
    border-radius: var(--radius);
    background: var(--panel-hi);
    border: 1px solid rgba(34, 229, 132, 0.25);
    box-shadow: 0 0 22px rgba(34, 229, 132, 0.06);
    cursor: pointer;
    animation: enter 0.4s ease;
}
.near:hover { border-color: rgba(34, 229, 132, 0.55); }
.compass { width: 74px; height: 74px; flex: 0 0 74px; position: relative; }
.compass svg { width: 100%; height: 100%; }
.compass .cd { position: absolute; inset: 0; display: grid; place-items: center; font-family: var(--mono); font-size: 12px; font-weight: 800; color: var(--ok); }
.near .info { flex: 1; min-width: 0; }
.near .nid { display: flex; align-items: center; gap: 10px; }
.near .nid .big { font-family: var(--mono); font-size: 17px; font-weight: 700; }
.near .nid .s { font-size: 12px; color: var(--muted); }
.near .nums { display: grid; grid-template-columns: repeat(3, 1fr); gap: 6px; margin-top: 10px; }
.near .nums div { background: rgba(255, 255, 255, 0.03); border-radius: 8px; padding: 5px 7px; }
.near .nums .k { font-size: 9.5px; letter-spacing: 0.1em; color: var(--dim); font-weight: 700; text-transform: uppercase; }
.near .nums .v { font-family: var(--mono); font-size: 13px; font-weight: 700; }

.terms { display: flex; gap: 6px; flex-wrap: wrap; align-items: center; margin-bottom: 14px; font-size: 12px; color: var(--muted); }
.terms span.t { font-family: var(--mono); padding: 3px 9px; border-radius: 999px; background: rgba(244, 63, 94, 0.1); border: 1px solid rgba(244, 63, 94, 0.35); color: #fecdd3; }
.terms .edit-terms { font-size: 12px; padding: 4px 11px; border-radius: 999px; margin-left: 4px; }
.terms-ed { margin: -4px 0 16px; padding: 14px; border-radius: 12px; border: 1px solid var(--border-hi); background: rgba(255, 255, 255, 0.02); }
.terms-ed[hidden] { display: none; }
.te-chips { display: flex; flex-wrap: wrap; gap: 6px; min-height: 30px; }
.te-chip { display: inline-flex; align-items: center; gap: 6px; font: 12.5px var(--mono); padding: 3px 4px 3px 10px; border-radius: 999px; background: rgba(244, 63, 94, 0.1); border: 1px solid rgba(244, 63, 94, 0.35); color: #fecdd3; }
.te-chip.new { border-style: dashed; }
.te-chip .n { font-size: 10.5px; color: var(--muted); }
.te-chip .n.hot { color: #fbbf24; }
.te-chip button { border: 0; background: rgba(255, 255, 255, 0.06); color: var(--muted); width: 20px; height: 20px; padding: 0; border-radius: 50%; font-size: 13px; line-height: 1; cursor: pointer; }
.te-chip button:hover { background: rgba(244, 63, 94, 0.35); color: #fff; }
.te-empty { font-size: 12.5px; color: var(--dim); align-self: center; }
.te-add { display: flex; gap: 8px; margin-top: 12px; flex-wrap: wrap; }
.te-add input { flex: 1 1 220px; min-width: 0; font: 13px var(--mono); padding: 8px 11px; border-radius: 9px; border: 1px solid var(--border); background: var(--bg, #070b12); color: var(--text); }
.te-add input:focus { outline: none; border-color: var(--border-hi); }
.te-hint { margin-top: 7px; font-size: 12px; color: var(--muted); min-height: 1.3em; }
.te-hint b { color: var(--text); }
.te-hint.warn b { color: #fbbf24; }
.te-actions { display: flex; gap: 8px; align-items: center; margin-top: 12px; flex-wrap: wrap; }
.te-actions .primary { color: #06130b; background: var(--ok); border-color: var(--ok); font-weight: 700; }
.te-actions .primary:disabled { opacity: 0.45; cursor: default; }
.te-actions .note { font-size: 12px; color: var(--dim); margin-left: auto; }
.m-meta-top { display: flex; align-items: center; justify-content: flex-end; gap: 8px; }
.star {
    border: 0;
    background: transparent;
    padding: 0 2px;
    margin: -4px -4px 0 0;
    font-size: 19px;
    line-height: 1;
    color: var(--dim);
    cursor: pointer;
    transition: color 0.15s, transform 0.15s;
}
.star:hover { color: #fbbf24; transform: scale(1.15); }
.star.on { color: #fbbf24; text-shadow: 0 0 10px rgba(251, 191, 36, 0.55); }
.msg.starred { border-color: rgba(251, 191, 36, 0.55); box-shadow: inset 0 0 0 1px rgba(251, 191, 36, 0.18); }
.alerts-tools { display: inline-flex; align-items: center; gap: 10px; letter-spacing: 0; text-transform: none; font-weight: 500; }
.alerts-tools .r { font-family: var(--mono); font-size: 11.5px; color: var(--dim); }
#alerts-reset { font-size: 12px; padding: 5px 11px; border-radius: 9px; }
#alerts-reset.confirm { color: #fca5a5; border-color: rgba(248, 113, 113, 0.6); background: rgba(248, 113, 113, 0.1); }
.alert-feed { display: grid; grid-template-columns: repeat(auto-fill, minmax(420px, 1fr)); gap: 10px; }

/* ---------- Decoded messages ---------- */
.m-dec {
    margin: 9px 0 0;
    font-size: 13px;
    line-height: 1.45;
    color: var(--text);
    padding: 7px 10px;
    border-radius: 8px;
    background: rgba(56, 189, 248, 0.06);
    border: 1px solid rgba(56, 189, 248, 0.16);
}
.m-text.raw { max-height: 4.9em; color: var(--muted); }
.chip.pos { color: var(--acars); border-color: color-mix(in srgb, var(--acars) 40%, transparent); background: color-mix(in srgb, var(--acars) 8%, transparent); cursor: pointer; }
.chip.pos:hover { background: color-mix(in srgb, var(--acars) 16%, transparent); }
.ntog { border-radius: 999px; padding: 5px 11px; font-size: 12px; }
.ntog.on { color: var(--adsb); border-color: color-mix(in srgb, var(--adsb) 50%, transparent); background: color-mix(in srgb, var(--adsb) 12%, transparent); }

/* ---------- ACARS position markers ---------- */
.ap { position: relative; width: 100%; height: 100%; --c: #fbbf24; }
.ap.s-vdlm2 { --c: #a78bfa; }
.ap i {
    position: absolute;
    inset: 3px;
    transform: rotate(45deg);
    border: 2px solid var(--c);
    border-radius: 2px;
    background: color-mix(in srgb, var(--c) 30%, transparent);
    box-shadow: 0 0 8px var(--c);
}
.legend-diamond { background: transparent !important; border: 2px solid #fbbf24; border-radius: 2px !important; transform: rotate(45deg) scale(0.85); }
.pop-note { margin-top: 6px; color: var(--acars); font-size: 11.5px; }
.pop-sum { margin-top: 6px; font-size: 12px; color: var(--text); max-width: 260px; white-space: normal; }

/* ---------- Trends ---------- */
.trend-head { display: flex; align-items: center; gap: 12px; flex-wrap: wrap; margin-bottom: 14px; }
.trend-head .r { font-family: var(--mono); font-size: 11.5px; color: var(--dim); }
.seg { display: inline-flex; gap: 4px; padding: 4px; border-radius: 12px; background: var(--panel); border: 1px solid var(--border); }
.seg button { border: 0; background: transparent; padding: 6px 12px; }
.seg button.on { background: rgba(255, 255, 255, 0.09); color: var(--text); }
.t-kpis { margin-top: 0; }
.trend-grid { display: grid; grid-template-columns: repeat(3, minmax(0, 1fr)); gap: 14px; align-items: start; }
.trend-grid .wide { grid-column: 1 / -1; }
.lg { display: flex; gap: 12px; font-family: var(--sans); letter-spacing: 0; text-transform: none; font-weight: 500; color: var(--muted); }
.lgi { display: inline-flex; align-items: center; gap: 6px; }
.lgi i { width: 10px; height: 10px; border-radius: 3px; display: inline-block; }
.chart { position: relative; }
.chart svg { display: block; width: 100%; }
.chart .gl { stroke: rgba(255, 255, 255, 0.06); stroke-width: 1; }
.chart .base { stroke: rgba(255, 255, 255, 0.2); stroke-width: 1; }
.chart .yt { fill: var(--dim); font: 10px var(--mono); text-anchor: end; }
.chart .xt { fill: var(--dim); font: 10px var(--mono); text-anchor: middle; }
.chart .hit { fill: transparent; cursor: crosshair; }
.chart .hit:hover { fill: rgba(255, 255, 255, 0.045); }
.ctip {
    position: absolute;
    z-index: 5;
    pointer-events: none;
    min-width: 150px;
    padding: 8px 10px;
    border-radius: 10px;
    background: rgba(9, 14, 22, 0.97);
    border: 1px solid var(--border-hi);
    box-shadow: 0 10px 30px rgba(0, 0, 0, 0.55);
    font-size: 12px;
    white-space: nowrap;
}
.ctip[hidden] { display: none; }
.ctip .tt { font-weight: 700; margin-bottom: 4px; color: var(--text); }
.ctip .row { display: flex; justify-content: space-between; gap: 14px; color: var(--muted); }
.ctip .row span:last-child { font-family: var(--mono); color: var(--text); }
.ctip .row i { display: inline-block; width: 8px; height: 8px; border-radius: 2px; margin-right: 6px; }
.hb-row { display: grid; grid-template-columns: minmax(0, 1fr) minmax(0, 1.1fr) 56px; gap: 10px; align-items: center; padding: 4px 0; font-size: 12.5px; }
.hb-row .nm { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.hb-row .n { font-family: var(--mono); text-align: right; color: var(--muted); }
.hb-row .track div { background: var(--c, #94a3b8); }
@media (max-width: 1100px) { .trend-grid { grid-template-columns: minmax(0, 1fr) minmax(0, 1fr); } }
@media (max-width: 760px) { .trend-grid { grid-template-columns: 1fr; } }

/* ---------- Routes ---------- */
.chip.rt { color: var(--text); border-color: rgba(232, 238, 246, 0.25); background: rgba(232, 238, 246, 0.05); }
.chip.rt.radio { color: var(--ok); border-color: rgba(34, 229, 132, 0.4); background: rgba(34, 229, 132, 0.07); }
.rt-inline { color: var(--text); font-weight: 600; }
.pop-route { margin: 4px 0 6px; font-size: 13px; font-weight: 700; color: var(--text); }
.pop-route small { display: block; font-weight: 500; color: var(--muted); font-size: 11.5px; margin-top: 1px; white-space: normal; max-width: 260px; }
.pop-rsrc { font-size: 11px; color: var(--dim); margin-bottom: 4px; max-width: 260px; white-space: normal; }
.pop-rsrc.radio { color: var(--ok); }
.ap-lbl {
    display: inline-block;
    transform: translate(-50%, -50%);
    padding: 1px 6px;
    border-radius: 6px;
    font: 700 11px var(--mono);
    color: #0b1220;
    background: #e8eef6;
    box-shadow: 0 0 0 2px rgba(9, 14, 22, 0.9);
    white-space: nowrap;
}
.lg-line { display: inline-block; width: 18px; height: 0; border-top: 2px solid #e8eef6; vertical-align: middle; margin-right: 8px; }
.lg-line.dash { border-top: 2px dashed #9fb0c8; }

/* ---------- Airport events (DEP / ARR) ---------- */
.apx {
    display: inline-flex;
    align-items: center;
    gap: 3px;
    margin-left: 6px;
    padding: 0 6px;
    border-radius: 5px;
    font: 700 9.5px var(--mono);
    letter-spacing: 0.03em;
    vertical-align: 1px;
    white-space: nowrap;
}
.apx.dep { color: #34d399; border: 1px solid rgba(52, 211, 153, 0.5); background: rgba(52, 211, 153, 0.1); }
.apx.arr { color: #fb923c; border: 1px solid rgba(251, 146, 60, 0.5); background: rgba(251, 146, 60, 0.1); }
.apx.fresh { animation: apxPulse 1.6s ease-in-out 3; }
@keyframes apxPulse { 50% { box-shadow: 0 0 0 3px rgba(255, 255, 255, 0.12); } }

/* ---------- Radar ---------- */
.map-ctl { flex-wrap: wrap; justify-content: flex-end; max-width: calc(100% - 24px); }
.radar-info {
    position: absolute;
    top: 52px;
    right: 12px;
    z-index: 500;
    padding: 4px 9px;
    border-radius: 8px;
    font: 600 11px var(--mono);
    color: var(--muted);
    background: rgba(10, 15, 24, 0.88);
    border: 1px solid var(--border);
}
.radar-info[hidden] { display: none; }

/* ---------- Flight timeline drawer ---------- */
.tl-link { cursor: pointer; }
.tl-link:hover { text-decoration: underline; text-decoration-color: rgba(232, 238, 246, 0.4); text-underline-offset: 3px; }
.drawer-bg { position: fixed; inset: 0; z-index: 1900; background: rgba(2, 6, 12, 0.55); backdrop-filter: blur(2px); }
.drawer {
    position: fixed;
    top: 0;
    right: 0;
    bottom: 0;
    z-index: 2000;
    width: min(560px, 100vw);
    overflow-y: auto;
    background: #0c121c;
    border-left: 1px solid var(--border-hi);
    box-shadow: -20px 0 50px rgba(0, 0, 0, 0.5);
    padding: 18px 20px 40px;
    animation: drawerIn 0.22s ease-out;
}
@keyframes drawerIn { from { transform: translateX(30px); opacity: 0; } }
.drawer[hidden], .drawer-bg[hidden] { display: none; }
.dr-head { display: flex; align-items: center; gap: 12px; }
.dr-head .av { width: 44px; height: 44px; flex-basis: 44px; }
.dr-id { min-width: 0; flex: 1; }
.dr-id .big { font: 700 20px var(--mono); }
.dr-id .big small { font-size: 13px; color: var(--muted); font-weight: 500; margin-left: 8px; }
.dr-id .s { color: var(--muted); font-size: 12.5px; }
.dr-close { border-radius: 10px; padding: 6px 11px; }
.dr-actions { display: flex; gap: 8px; margin: 12px 0 4px; flex-wrap: wrap; }
.dr-actions button, .dr-actions a { font-size: 12px; padding: 6px 11px; border-radius: 9px; }
.dr-actions a { display: inline-block; text-decoration: none; color: var(--text); border: 1px solid var(--border); background: rgba(255, 255, 255, 0.03); }
.dr-actions a:hover { border-color: var(--border-hi); }
.dr-sec { margin-top: 18px; }
.dr-sec h4 { margin: 0 0 8px; font: 700 11px var(--sans); letter-spacing: 0.08em; text-transform: uppercase; color: var(--dim); display: flex; justify-content: space-between; }
.dr-sec h4 span { font-family: var(--mono); letter-spacing: 0; text-transform: none; font-weight: 500; }
.dr-route { font-size: 15px; font-weight: 700; }
.dr-route small { display: block; font-size: 12.5px; font-weight: 500; color: var(--muted); margin-top: 2px; }
.oooi { display: grid; grid-template-columns: repeat(4, minmax(0, 1fr)); gap: 8px; }
.oooi > div { padding: 9px 10px; border-radius: 10px; background: var(--panel); border: 1px solid var(--border); }
.oooi .k { font: 700 10px var(--sans); letter-spacing: 0.08em; color: var(--dim); }
.oooi .v { font: 700 15px var(--mono); margin-top: 3px; }
.oooi .z { font: 500 10.5px var(--mono); color: var(--dim); }
.oooi .na { color: var(--dim); }
@media (max-width: 480px) { .oooi { gap: 6px; } .oooi > div { padding: 8px 7px; } .oooi .v { font-size: 13px; white-space: nowrap; } .oooi .z { font-size: 9.5px; } }
.durs { display: flex; gap: 16px; margin-top: 8px; font-size: 12.5px; color: var(--muted); flex-wrap: wrap; }
.durs b { color: var(--text); font-family: var(--mono); }
.prof { position: relative; }
.prof svg { display: block; width: 100%; }
.prof .gl { stroke: rgba(255, 255, 255, 0.06); }
.prof .base { stroke: rgba(255, 255, 255, 0.2); }
.prof .yt { fill: var(--dim); font: 10px var(--mono); text-anchor: end; }
.prof .xt { fill: var(--dim); font: 10px var(--mono); text-anchor: middle; }
.prof .cross { stroke: rgba(255, 255, 255, 0.35); stroke-width: 1; }
.tl-list { position: relative; margin-left: 6px; border-left: 2px solid rgba(255, 255, 255, 0.08); }
.tl-item { position: relative; padding: 2px 0 14px 16px; }
.tl-item::before {
    content: "";
    position: absolute;
    left: -6px;
    top: 6px;
    width: 10px;
    height: 10px;
    border-radius: 50%;
    background: #64748b;
    box-shadow: 0 0 0 3px #0c121c;
}
.tl-item.s-acars::before { background: var(--acars); }
.tl-item.s-vdlm2::before { background: var(--vdlm2); }
.tl-item.ev::before { background: #e8eef6; }
.tl-item.ev.dep::before { background: #34d399; }
.tl-item.ev.arr::before { background: #fb923c; }
.tl-item.oooi-ev::before { width: 12px; height: 12px; left: -7px; border-radius: 3px; background: #e8eef6; }
.tl-top { display: flex; gap: 8px; align-items: baseline; flex-wrap: wrap; font-size: 12px; color: var(--muted); }
.tl-top .t { font: 700 12.5px var(--mono); color: var(--text); }
.tl-top .src { font: 700 10px var(--mono); letter-spacing: 0.05em; }
.tl-item.s-acars .src { color: var(--acars); }
.tl-item.s-vdlm2 .src { color: var(--vdlm2); }
.tl-dec { margin-top: 4px; font-size: 13px; color: var(--text); }
.tl-raw { margin: 5px 0 0; padding: 6px 8px; border-radius: 8px; background: rgba(255, 255, 255, 0.03); font: 11.5px/1.45 var(--mono); color: var(--muted); white-space: pre-wrap; word-break: break-word; max-height: 4.4em; overflow: hidden; cursor: pointer; }
.tl-raw.open { max-height: none; }
.tl-hide { font-size: 12px; color: var(--dim); }
.tl-empty { font-size: 12.5px; color: var(--dim); }

/* ---------- Toasts ---------- */
.toasts { position: fixed; bottom: 16px; right: 16px; z-index: 2000; display: grid; gap: 8px; width: 330px; max-width: calc(100vw - 32px); }
.toast {
    --c: var(--ok);
    display: flex;
    gap: 11px;
    align-items: center;
    padding: 11px 13px;
    border-radius: 12px;
    background: rgba(9, 14, 22, 0.97);
    border: 1px solid color-mix(in srgb, var(--c) 45%, transparent);
    box-shadow: 0 12px 40px rgba(0, 0, 0, 0.6), 0 0 26px color-mix(in srgb, var(--c) 18%, transparent);
    animation: slidein 0.35s ease both;
    cursor: pointer;
}
.toast.out { animation: slideout 0.35s ease both; }
.toast .tt { font-size: 10px; font-weight: 800; letter-spacing: 0.14em; color: var(--c); }
.toast .tc { font-family: var(--mono); font-weight: 700; font-size: 14px; }
.toast .td { color: var(--muted); font-size: 12px; }
@keyframes slidein { from { opacity: 0; transform: translateX(30px); } to { opacity: 1; transform: none; } }
@keyframes slideout { to { opacity: 0; transform: translateX(30px); } }

footer { display: flex; justify-content: space-between; gap: 12px; flex-wrap: wrap; color: var(--dim); font-size: 11.5px; font-family: var(--mono); margin: 22px 0 28px; }

/* ---------- Responsive ---------- */
@media (max-width: 1350px) {
    .live-grid { grid-template-columns: minmax(0, 1.3fr) minmax(0, 1fr); }
    .live-grid > .col:last-child { grid-column: 2; }
    .kpis { grid-template-columns: repeat(3, minmax(0, 1fr)); }
}
@media (max-width: 1350px) and (min-width: 901px) {
    .live-grid { grid-template-areas: "feed a" "feed b"; }
    .live-grid > .feed-panel { grid-area: feed; }
    .live-grid > .col:nth-child(2) { grid-area: a; }
    .live-grid > .col:nth-child(3) { grid-area: b; }
}
@media (max-width: 900px) {
    .live-grid { grid-template-columns: 1fr; }
    .live-grid > .col:last-child { grid-column: auto; }
    .alert-feed { grid-template-columns: 1fr; }
    .clock { display: none; }
}
@media (max-width: 640px) {
    .kpis { grid-template-columns: repeat(2, minmax(0, 1fr)); }
    .kpi .spark { display: none; }
    .kpi .v { font-size: 22px; }
    .tabs { position: static; }
    .sub { display: none; }
    #map { height: 70vh; min-height: 360px; }
    input[type="search"] { width: 100%; }
}
@media (prefers-reduced-motion: reduce) {
    *, *::before, *::after { animation: none !important; transition: none !important; }
}
</style>
</head>
<body>

<header class="top">
    <div class="wrap head">
        <div class="brand">
            <div class="logo">
                <svg viewBox="0 0 24 24" fill="none" stroke="#fbbf24" stroke-width="1.8" stroke-linecap="round">
                    <path d="M12 12v9M9 21h6"/><circle cx="12" cy="10" r="1.6" fill="#fbbf24"/>
                    <path d="M8.5 6.5a5 5 0 0 0 0 7M15.5 6.5a5 5 0 0 1 0 7" stroke="#a78bfa"/>
                    <path d="M5.6 3.6a9 9 0 0 0 0 12.8M18.4 3.6a9 9 0 0 1 0 12.8" stroke="#a78bfa" opacity=".6"/>
                </svg>
            </div>
            <div>
                <h1>Live Aviation Dashboard</h1>
                <div class="sub"><b style="color:var(--acars)">ACARS</b> &middot; <b style="color:var(--vdlm2)">VDLM2</b> &middot; <b style="color:var(--adsb)">ADS-B</b> &middot; up <span id="uptime">--</span></div>
            </div>
        </div>
        <div class="wx" id="wx" hidden></div>
        <div class="lights">
            <span class="light" id="l-acars" title="ACARS" style="--c: var(--acars)"><i></i>ACARS</span>
            <span class="light" id="l-vdlm2" title="VDLM2" style="--c: var(--vdlm2)"><i></i>VDLM2</span>
            <span class="light" id="l-adsb" title="ADSB" style="--c: var(--adsb)"><i></i>ADS-B</span>
            <span class="light" id="l-link" title="Dashboard link" style="--c: var(--ok)"><i></i>LINK</span>
        </div>
        <div class="clock">
            <div><div class="t" id="clock-local">--:--:--</div><div class="l">Local</div></div>
            <div><div class="t" id="clock-utc" style="color: var(--muted)">--:--:--</div><div class="l">Zulu</div></div>
        </div>
    </div>
</header>

<main class="wrap">

    <div class="emg-banner" id="emg-banner" hidden role="alert">
        <span class="e-title">&#9888; EMERGENCY</span>
        <div id="emg-items" style="display:flex;gap:8px;flex-wrap:wrap"></div>
    </div>

    <div class="watch" id="watch" hidden>
        <span class="w-title"><i></i>TRACKED AIRCRAFT</span>
        <div class="w-items" id="watch-items"></div>
    </div>

    <section class="kpis" id="kpis">
        <div class="kpi" style="--c: var(--text)">
            <div class="k">Messages</div>
            <div class="v" id="k-total">0</div>
            <div class="h" id="k-total-h">all time</div>
        </div>
        <div class="kpi" style="--c: var(--ok)">
            <div class="k">Verified</div>
            <div class="v" id="k-verified">0</div>
            <div class="meter"><div id="k-verified-m" style="width: 0%"></div></div>
            <div class="h" id="k-verified-h">matched to ADS-B</div>
        </div>
        <div class="kpi" style="--c: var(--acars)">
            <div class="k">Radio Rate</div>
            <div class="v"><span id="k-radio">0.0</span><small> /min</small></div>
            <div class="h" id="k-radio-h">ACARS 0 &middot; VDLM2 0</div>
            <div class="spark" id="spark-radio"></div>
        </div>
        <div class="kpi" style="--c: var(--adsb)">
            <div class="k">ADS-B Aircraft</div>
            <div class="v" id="k-aircraft">0</div>
            <div class="h" id="k-aircraft-h">0 msg/s</div>
            <div class="spark" id="spark-adsb"></div>
        </div>
        <div class="kpi" style="--c: #34d399">
            <div class="k">Nearby</div>
            <div class="v" id="k-nearby">0</div>
            <div class="h">&le; 20 mi, below 5,000 ft</div>
        </div>
        <div class="kpi" style="--c: var(--alert)">
            <div class="k">Alerts</div>
            <div class="v" id="k-alerts">0</div>
            <div class="h" id="k-alerts-h">keyword matches</div>
        </div>
    </section>

    <nav class="tabs" id="tabs">
        <button class="tab on" data-tab="live">
            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><path d="M3 12h4l3-8 4 16 3-8h4"/></svg>Live
        </button>
        <button class="tab" data-tab="map">
            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><path d="m9 4-6 3v13l6-3 6 3 6-3V4l-6 3-6-3zM9 4v13M15 7v13"/></svg>Map
        </button>
        <button class="tab" data-tab="nearby">
            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><circle cx="12" cy="12" r="3"/><circle cx="12" cy="12" r="8" opacity=".5"/></svg>Nearby <span class="badge" id="b-nearby">0</span>
        </button>
        <button class="tab" data-tab="alerts">
            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><path d="M12 3 2 20h20L12 3zM12 10v4M12 17v.5"/></svg>Alerts <span class="badge" id="b-alerts">0</span>
        </button>
        <button class="tab" data-tab="trends">
            <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><path d="M4 20V10M10 20V4M16 20v-7M22 20H2"/></svg>Trends
        </button>
    </nav>

    <!-- LIVE -->
    <section class="view live-grid" id="v-live">
        <div class="panel feed-panel">
            <div class="panel-title"><span>Message Feed</span><span class="r" id="feed-count"></span></div>
            <div class="feed-tools">
                <button class="fchip on" data-filter="all">All</button>
                <button class="fchip" data-filter="acars">ACARS</button>
                <button class="fchip" data-filter="vdlm2">VDLM2</button>
                <button class="fchip" data-filter="verified">&#10003; Verified</button>
                <button class="fchip" data-filter="alerts">Alerts</button>
                <button class="ntog" id="noise" title="Hide link tests, squitters, link-management frames and empty messages">Hide noise</button>
                <span class="grow"></span>
                <input type="search" id="q" placeholder="Search flight, tail, text&hellip;" autocomplete="off">
                <button id="pause" title="Pause the live feed">&#10074;&#10074; Pause</button>
            </div>
            <button class="pending" id="pending"></button>
            <div class="feed" id="feed"></div>
        </div>

        <div class="col">
            <div class="panel">
                <div class="panel-title"><span>Verified by Distance</span><span class="r">miles from home</span></div>
                <div class="dist" id="dist"></div>
                <div class="dist-labels"><span>0&ndash;25</span><span>25&ndash;50</span><span>50&ndash;100</span><span>100&ndash;200</span><span>200+</span></div>
            </div>
            <div class="panel">
                <div class="panel-title"><span>Frequencies</span><span class="r" id="freq-count"></span></div>
                <div id="freqs"></div>
            </div>
            <div class="panel">
                <div class="panel-title"><span>Airlines</span><span class="r">messages</span></div>
                <div id="airlines"></div>
            </div>
        </div>

        <div class="col">
            <div class="panel">
                <div class="panel-title"><span>ADS-B Traffic</span><span class="r" id="ac-count">nearest first</span></div>
                <div class="ac-list" id="ac-list"></div>
            </div>
        </div>
    </section>

    <!-- MAP -->
    <section class="view" id="v-map" hidden>
        <div class="map-wrap">
            <div id="map"></div>
            <div class="map-ctl">
                <button id="m-labels" class="on">Labels</button>
                <button id="m-pos" class="on" title="Positions reported over ACARS / VDLM2 for aircraft not seen on ADS-B">Positions</button>
                <button id="m-trails" title="Show the flown path of every aircraft">Trails</button>
                <button id="m-cov" title="Farthest ACARS and VDLM2 reception in each direction">Coverage</button>
                <button id="m-radar" title="Weather radar (RainViewer)">Radar</button>
                <button id="m-loop" hidden title="Animate the last 2 hours of radar">Loop</button>
                <button id="m-fit">Fit</button>
                <button id="m-home">Home</button>
            </div>
            <div class="radar-info" id="radar-info" hidden></div>
            <div class="map-legend">
                <div class="ttl" id="m-count">0 aircraft</div>
                <div><i style="background:#38bdf8"></i>Below 10,000 ft</div>
                <div><i style="background:#a78bfa"></i>10,000&ndash;25,000 ft</div>
                <div><i style="background:#fbbf24"></i>Above 25,000 ft</div>
                <div><i style="background:#94a3b8"></i>On ground / unknown</div>
                <div><i style="background:#22e584; box-shadow: 0 0 8px #22e584"></i>Verified radio contact</div>
                <div><i class="legend-diamond"></i>Radio-reported position (no ADS-B)</div>
                <div><span class="lg-heli" id="lg-heli"></span>Helicopter</div>
                <div><span class="lg-line"></span>Flown path &middot; route (click a plane)</div>
                <div><span class="lg-line dash"></span>Remaining route to destination</div>
                <div class="cov-legend" id="cov-lg-a" hidden><span class="lg-cov" style="--c:#fbbf24"></span><span id="cov-lg-a-t">ACARS coverage</span></div>
                <div class="cov-legend" id="cov-lg-v" hidden><span class="lg-cov" style="--c:#a78bfa"></span><span id="cov-lg-v-t">VDLM2 coverage</span></div>
            </div>
        </div>
    </section>

    <!-- NEARBY -->
    <section class="view" id="v-nearby" hidden>
        <div class="panel">
            <div class="panel-title"><span>Nearby Aircraft</span><span class="r">&le; 20 mi from home &middot; below 5,000 ft</span></div>
            <div class="near-grid" id="nearby"></div>
        </div>
    </section>

    <!-- ALERTS -->
    <section class="view" id="v-alerts" hidden>
        <div class="panel">
            <div class="panel-title"><span>Alert Messages</span><span class="alerts-tools"><span class="r" id="alerts-count"></span><button id="alerts-reset" title="Delete all alerts except starred ones and reset the alert count">Reset alerts</button></span></div>
            <div class="terms" id="terms"></div>
            <div class="terms-ed" id="terms-ed" hidden></div>
            <div class="alert-feed" id="alert-feed"></div>
        </div>
    </section>

    <!-- TRENDS -->
    <section class="view" id="v-trends" hidden>
        <div class="trend-head">
            <div class="seg" id="t-range">
                <button data-days="7" class="on">7 days</button>
                <button data-days="30">30 days</button>
                <button data-days="90">90 days</button>
            </div>
            <span class="r" id="t-note">Loading&hellip;</span>
        </div>
        <section class="kpis t-kpis" id="t-kpis"></section>
        <div class="trend-grid">
            <div class="panel wide">
                <div class="panel-title"><span>Messages per hour &middot; last 48 h</span><span class="lg" id="lg-hourly"></span></div>
                <div class="chart" id="c-hourly"></div>
            </div>
            <div class="panel wide">
                <div class="panel-title"><span>Messages per day</span><span class="lg" id="lg-daily"></span></div>
                <div class="chart" id="c-daily"></div>
            </div>
            <div class="panel">
                <div class="panel-title"><span>Typical day</span><span class="r">avg messages by local hour</span></div>
                <div class="chart" id="c-hod"></div>
            </div>
            <div class="panel">
                <div class="panel-title"><span>Message types</span><span class="r">this period</span></div>
                <div id="c-types"></div>
            </div>
            <div class="panel">
                <div class="panel-title"><span>Top airlines</span><span class="r">this period</span></div>
                <div id="c-airlines"></div>
            </div>
        </div>
    </section>

    <div class="drawer-bg" id="dr-bg" hidden></div>
    <aside class="drawer" id="drawer" hidden aria-label="Flight timeline"></aside>

    <footer>
        <span id="foot-left">Connecting&hellip;</span>
        <span>Home %%HOME_LAT%%, %%HOME_LON%%</span>
    </footer>
</main>

<div class="toasts" id="toasts"></div>

<script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js" crossorigin=""></script>
<script>
const HOME_LAT = %%HOME_LAT%%;
const HOME_LON = %%HOME_LON%%;
const WS_PORT = %%WS_PORT%%;
const NEAR_MILES = 20;
const NEAR_ALT = 5000;
const MAX_FEED = 300;
const MAX_ALERTS = 200;
const FEED_DOM_LIMIT = 150;

const AIRLINE_MAP = {
    "AA": "American Airlines", "AAL": "American Airlines",
    "UA": "United Airlines",   "UAL": "United Airlines",
    "DL": "Delta Air Lines",   "DAL": "Delta Air Lines",
    "WN": "Southwest Airlines","SWA": "Southwest Airlines",
    "AS": "Alaska Airlines",   "ASA": "Alaska Airlines",
    "B6": "JetBlue Airways",   "JBU": "JetBlue Airways",
    "F9": "Frontier Airlines", "FFT": "Frontier Airlines",
    "NK": "Spirit Airlines",   "NKS": "Spirit Airlines",
    "OO": "SkyWest Airlines",  "SKW": "SkyWest Airlines",
    "MQ": "Envoy Air",         "ENY": "Envoy Air",
    "FX": "FedEx Express",     "FDX": "FedEx Express",
    "5X": "UPS Airlines",      "UPS": "UPS Airlines",
};

const LOGO_MAP = {
    "American Airlines": "/static/airlines/aa.png",
    "United Airlines": "/static/airlines/ua.png",
    "Delta Air Lines": "/static/airlines/dl.png",
    "Southwest Airlines": "/static/airlines/wn.png",
    "Alaska Airlines": "/static/airlines/as.png",
    "JetBlue Airways": "/static/airlines/b6.png",
    "Frontier Airlines": "/static/airlines/f9.png",
    "Spirit Airlines": "/static/airlines/nk.png",
    "SkyWest Airlines": "/static/airlines/oo.png",
    "Envoy Air": "/static/airlines/mq.png",
    "FedEx Express": "/static/airlines/fx.png",
    "UPS Airlines": "/static/airlines/ups.png",
};

const $ = id => document.getElementById(id);

const S = {
    messages: [],
    alerts: [],
    aircraft: [],
    acByHex: new Map(),
    verified: new Set(),
    watch: [],
    watchSeen: new Set(),
    terms: [],
    termRe: null,
    filter: "all",
    q: "",
    paused: false,
    pending: 0,
    tab: "live",
    unseenAlerts: 0,
    labels: true,
    radioHist: [],
    adsbHist: [],
    lastSpark: 0,
    status: null,
    prevAirlines: new Map(),
    positions: [],
    posByKey: new Map(),
    adsbRegs: new Set(),
    adsbFlights: new Set(),
    showPos: true,
    hideNoise: false,
    routes: {},
    events: {},
    emerg: {},
    emergSeen: new Set(),
    showCov: false,
    sel: null,
    showTrails: false,
    dr: null,
};

const T = { days: 7, data: null, last: 0, loading: false };

/* ---------- Helpers ---------- */
function esc(v) {
    if (v === null || v === undefined) return "";
    return String(v).replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;").replaceAll('"', "&quot;").replaceAll("'", "&#039;");
}

function num(v) {
    if (v === null || v === undefined || v === "") return null;
    const n = Number(v);
    return Number.isFinite(n) ? n : null;
}

function hashHue(s) {
    let h = 0;
    for (const ch of String(s)) h = (h * 31 + ch.codePointAt(0)) >>> 0;
    return h % 360;
}

function distMiles(lat1, lon1, lat2, lon2) {
    const R = 3958.8, r = d => d * Math.PI / 180;
    const dLat = r(lat2 - lat1), dLon = r(lon2 - lon1);
    const a = Math.sin(dLat / 2) ** 2 + Math.cos(r(lat1)) * Math.cos(r(lat2)) * Math.sin(dLon / 2) ** 2;
    return R * 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
}

function bearing(lat1, lon1, lat2, lon2) {
    const r = d => d * Math.PI / 180;
    const x = Math.sin(r(lon2 - lon1)) * Math.cos(r(lat2));
    const y = Math.cos(r(lat1)) * Math.sin(r(lat2)) - Math.sin(r(lat1)) * Math.cos(r(lat2)) * Math.cos(r(lon2 - lon1));
    return (Math.atan2(x, y) * 180 / Math.PI + 360) % 360;
}

function cardinal(d) {
    return ["N","NNE","NE","ENE","E","ESE","SE","SSE","S","SSW","SW","WSW","W","WNW","NW","NNW"][Math.round(d / 22.5) % 16];
}

function airlineFromFlight(f) {
    if (!f) return null;
    const up = String(f).toUpperCase().trim();
    return AIRLINE_MAP[up.slice(0, 2)] || AIRLINE_MAP[up.slice(0, 3)] || null;
}

function timeAgo(ts) {
    if (!ts) return "";
    const s = Math.max(0, Date.now() / 1000 - ts);
    if (s < 60) return Math.floor(s) + "s ago";
    if (s < 3600) return Math.floor(s / 60) + "m ago";
    if (s < 86400) return Math.floor(s / 3600) + "h ago";
    return Math.floor(s / 86400) + "d ago";
}

function setNum(id, value) {
    const el = $(id);
    const t = String(value);
    if (el.textContent === t) return;
    el.textContent = t;
    el.classList.remove("bump");
    void el.offsetWidth;
    el.classList.add("bump");
}

function avatar(airline, ident) {
    let label;
    if (airline) {
        label = airline.split(/\s+/).filter(w => /^[A-Za-z]/.test(w)).map(w => w[0]).join("").slice(0, 2).toUpperCase();
    } else {
        label = String(ident || "").replace(/[^A-Za-z0-9]/g, "").slice(0, 2).toUpperCase() || "?";
    }
    const logo = airline ? LOGO_MAP[airline] : null;
    const useLogo = logo && !BAD_LOGOS.has(logo);
    return `<span class="av" style="--h:${hashHue(airline || ident || "?")}">${esc(label)}${useLogo ? `<img src="${logo}" alt="" onerror="badLogo(this)">` : ""}</span>`;
}

// Remember logos that failed to load so we don't re-request them on every refresh.
const BAD_LOGOS = new Set();
function badLogo(img) {
    BAD_LOGOS.add(img.getAttribute("src"));
    img.remove();
}

function altOf(ac) {
    const a = ac.alt_baro ?? ac.alt_geom;
    if (a === "ground") return 0;
    return num(a);
}

/* ---------- Helicopters ---------- */
// ICAO type designators for common helicopters (used when the aircraft doesn't broadcast category A7).
const HELI_TYPES = new Set((
    "R22 R44 R66 CABR B06 B06T B47G B105 B205 B212 B214 B222 B230 B407 B412 B427 B429 B430 B505 B525 " +
    "UH1 UH1Y H1 AS32 AS3B AS50 AS55 AS65 EC20 EC25 EC30 EC35 EC45 EC55 EC75 H125 H130 H135 H145 H155 H160 H175 H225 " +
    "BK17 A109 A119 A129 A139 A149 A169 A189 AW09 S61 S64 S70 S76 S92 H60 UH60 H47 H53 H64 H72 V22 " +
    "H269 H300 H500 H520 MD52 MD60 MD90 EXPL EN28 EN48 GAZL ALO2 ALO3 LAMA PUMA SUCO MI8 MI24 KA32 KMAX HUCO NH90 TIGR"
).split(" "));

function isHeli(ac) {
    if (!ac) return false;
    if (String(ac.category || "").toUpperCase() === "A7") return true;
    const t = String(ac.t || ac.type || "").trim().toUpperCase();
    if (t && HELI_TYPES.has(t)) return true;
    const desc = String(ac.desc || "").toUpperCase();
    return /HELICOPTER|COPTER|ROTORCRAFT/.test(desc);
}

// Top-down helicopter, nose up (rotated by track like the plane icon).
const HELI_SVG_INNER =
    '<circle class="hs disk" cx="12" cy="9.5" r="8.6"/>' +
    '<ellipse cx="12" cy="9.8" rx="2.9" ry="4.4"/>' +
    '<rect x="11.3" y="13" width="1.4" height="8.2" rx="0.6"/>' +
    '<rect x="9.4" y="20" width="5.2" height="1.4" rx="0.6"/>' +
    '<g class="hs blades"><line x1="4" y1="9.5" x2="20" y2="9.5"/><line x1="12" y1="1.5" x2="12" y2="17.5"/></g>';

function heliIcon(spin = false) {
    return `<svg viewBox="0 0 24 24">${spin ? HELI_SVG_INNER : HELI_SVG_INNER.replace("hs blades", "hs")}</svg>`;
}

function acAvatar(ac, airline, ident) {
    if (isHeli(ac) && !(airline && LOGO_MAP[airline])) return `<span class="av heli" title="Helicopter">${heliIcon(false)}</span>`;
    return avatar(airline, ident);
}

function identOf(ac) {
    return String(ac.flight || "").trim().toUpperCase() || String(ac.r || ac.reg || "").trim().toUpperCase() || String(ac.hex || "").toUpperCase();
}

/* ---------- Clock & lights ---------- */
function tick() {
    const d = new Date();
    $("clock-local").textContent = d.toLocaleTimeString([], { hour: "2-digit", minute: "2-digit", second: "2-digit", hour12: false });
    $("clock-utc").textContent = d.toISOString().slice(11, 19) + "Z";
    document.querySelectorAll("[data-ts]").forEach(el => { el.textContent = timeAgo(Number(el.dataset.ts)); });
}

function light(name, on) {
    $("l-" + name).classList.toggle("up", !!on);
}

/* ---------- Sparklines ---------- */
function sparkline(id, arr, color) {
    const el = $(id);
    if (arr.length < 2) { el.innerHTML = ""; return; }
    const w = 100, h = 30;
    const max = Math.max(...arr, 0.0001);
    const pts = arr.map((v, i) => `${(i / (arr.length - 1) * w).toFixed(1)},${(h - (v / max) * (h - 4) - 2).toFixed(1)}`).join(" ");
    el.innerHTML = `<svg viewBox="0 0 ${w} ${h}" preserveAspectRatio="none">
        <polygon points="0,${h} ${pts} ${w},${h}" fill="${color}" opacity=".13"/>
        <polyline points="${pts}" fill="none" stroke="${color}" stroke-width="1.6" vector-effect="non-scaling-stroke" stroke-linejoin="round"/>
    </svg>`;
}

/* ---------- Alert term highlighting ---------- */
function setTerms(terms) {
    const list = (terms || []).filter(Boolean);
    if (JSON.stringify(list) === JSON.stringify(S.terms)) return;
    S.terms = list;
    const parts = list.map(t => t.replace(/[.*+?^${}()|[\]\\]/g, "\\$&"));
    try {
        S.termRe = parts.length ? new RegExp(`(?<![A-Za-z0-9_])(?:${parts.join("|")})(?![A-Za-z0-9_])`, "gi") : null;
    } catch (e) {
        S.termRe = null;
    }
    $("terms").innerHTML = (list.length
        ? `Watching for: ${list.map(t => `<span class="t">${esc(t)}</span>`).join("")}`
        : `No alert words yet.`) + `<button class="edit-terms" id="edit-terms" title="Add, remove or change alert words">&#9998; Edit words</button>`;
    if (TE.open && !TE.dirty) { TE.list = list.slice(); renderTermsEditor(); }
}

/* ---------- Alert word editor ---------- */
const TE = { open: false, list: [], dirty: false, saving: false };

function termRegex(t) {
    const e = t.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    return new RegExp(`(?<![A-Za-z0-9_])${e}(?![A-Za-z0-9_])`, "i");
}

function recentMatches(t) {
    // how many of the messages currently in the feed this word would have flagged
    if (!t) return 0;
    let re;
    try { re = termRegex(t); } catch (e) { return 0; }
    let n = 0;
    for (const m of S.messages) if (re.test(msgText(m))) n++;
    return n;
}

function cleanTerm(t) {
    return String(t || "").replace(/\s+/g, " ").trim().toLowerCase().slice(0, 100);
}

function renderTermsEditor() {
    const el = $("terms-ed");
    if (!TE.open) { el.hidden = true; return; }
    el.hidden = false;
    const total = S.messages.length;
    const saved = new Set(S.terms);
    const chips = TE.list.map((t, i) => {
        const n = recentMatches(t);
        return `<span class="te-chip ${saved.has(t) ? "" : "new"}" title="${n} of the last ${total} messages matched">${esc(t)}<span class="n ${n > total * 0.05 && n > 3 ? "hot" : ""}">${n}</span><button data-te-del="${i}" title="Remove" aria-label="Remove ${esc(t)}">&times;</button></span>`;
    }).join("");
    el.innerHTML = `
        <div class="te-chips">${chips || '<span class="te-empty">No words. Add one below.</span>'}</div>
        <div class="te-add">
            <input id="te-input" type="text" maxlength="100" placeholder="Add a word or phrase, e.g. MEDICAL or DIVERT" autocomplete="off" spellcheck="false">
            <button id="te-add-btn">Add</button>
        </div>
        <div class="te-hint" id="te-hint">Whole-word match, not case sensitive. The number on each word is how many of the last ${total} messages it matched.</div>
        <div class="te-actions">
            <button class="primary" id="te-save" ${TE.dirty && !TE.saving ? "" : "disabled"}>${TE.saving ? "Saving&hellip;" : "Save"}</button>
            <button id="te-cancel">${TE.dirty ? "Discard changes" : "Close"}</button>
            <span class="note">${TE.dirty ? "Unsaved changes" : "Saved to alerts.txt on the Pi"}</span>
        </div>`;
}

function termHint() {
    const inp = $("te-input"), hint = $("te-hint");
    if (!inp || !hint) return;
    const t = cleanTerm(inp.value);
    const total = S.messages.length;
    if (!t) { hint.className = "te-hint"; hint.innerHTML = `Whole-word match, not case sensitive. The number on each word is how many of the last ${total} messages it matched.`; return; }
    if (TE.list.includes(t)) { hint.className = "te-hint"; hint.innerHTML = `<b>${esc(t)}</b> is already on the list.`; return; }
    const n = recentMatches(t);
    const noisy = n > total * 0.05 && n > 3;
    hint.className = "te-hint" + (noisy ? " warn" : "");
    hint.innerHTML = `<b>${esc(t)}</b> would have matched <b>${n}</b> of the last ${total} messages${noisy ? " — that could be a lot of alerts (and phone notifications)." : n ? "." : " — none recently, which is normal for rare words."}`;
}

function addTerm() {
    const inp = $("te-input");
    const t = cleanTerm(inp && inp.value);
    if (!t || t.startsWith("#") || TE.list.includes(t)) { termHint(); return; }
    TE.list.push(t);
    TE.dirty = true;
    renderTermsEditor();
    $("te-input").focus();
}

function openTermsEditor() {
    TE.open = true;
    TE.list = S.terms.slice();
    TE.dirty = false;
    renderTermsEditor();
    setTimeout(() => $("te-input") && $("te-input").focus(), 0);
}

function closeTermsEditor() {
    TE.open = false;
    TE.dirty = false;
    renderTermsEditor();
}

function saveTerms() {
    if (!(ws && ws.readyState === WebSocket.OPEN)) {
        toast({ kind: "info", title: "NOT SAVED", main: "Dashboard offline", detail: "Reconnect and try again." });
        return;
    }
    TE.saving = true;
    renderTermsEditor();
    ws.send(JSON.stringify({ type: "alert_terms_set", terms: TE.list }));
}

function onTermsSaved(p) {
    TE.saving = false;
    if (p.ok) {
        TE.dirty = false;
        closeTermsEditor();
        toast({ kind: "info", title: "ALERT WORDS SAVED", main: `${p.count} word${p.count === 1 ? "" : "s"}`, detail: "New messages are checked against the updated list." });
    } else {
        renderTermsEditor();
        toast({ kind: "info", title: "NOT SAVED", main: "Could not write alerts.txt", detail: String(p.error || "").slice(0, 80) });
    }
}

function highlight(text) {
    const s = String(text ?? "");
    if (!S.termRe) return esc(s);
    let out = "", last = 0;
    for (const m of s.matchAll(S.termRe)) {
        out += esc(s.slice(last, m.index)) + "<mark>" + esc(m[0]) + "</mark>";
        last = m.index + m[0].length;
    }
    return out + esc(s.slice(last));
}

/* ---------- Messages ---------- */
function msgText(m) {
    return m.msg_text || m.text || m.message || m.summary || "";
}

function chip(label, value) {
    return `<span class="chip"><b>${esc(label)}</b>${esc(value)}</span>`;
}

function rtCode(r, end) {
    return (end === "o" ? (r.o_iata || r.orig) : (r.d_iata || r.dest)) || "?";
}
function rtPlace(r, end) {
    const city = end === "o" ? r.o_city : r.d_city;
    const name = end === "o" ? r.o_name : r.d_name;
    return city || name || (end === "o" ? r.orig : r.dest);
}
function rtShort(r) { return `${rtCode(r, "o")} → ${rtCode(r, "d")}`; }
function rtLong(r) { return `${rtPlace(r, "o")} → ${rtPlace(r, "d")}`; }
function rtSourceNote(r) {
    return r.src === "radio"
        ? `✓ Reported by the aircraft${r.kind ? " (" + r.kind + ")" : ""}`
        : "Scheduled route (adsbdb.com) — may be wrong for diversions or charters";
}
function routeChip(r) {
    if (!r) return "";
    return `<span class="chip rt ${r.src === "radio" ? "radio" : ""}" title="${esc(rtLong(r) + " · " + rtSourceNote(r))}">${r.src === "radio" ? "&#10003; " : ""}&#9992; ${esc(rtShort(r))}</span>`;
}
function routePopupBlock(r) {
    if (!r) return "";
    return `<div class="pop-route">${esc(rtShort(r))}<small>${esc(rtLong(r))}</small></div>
        <div class="pop-rsrc ${r.src === "radio" ? "radio" : ""}">${esc(rtSourceNote(r))}</div>`;
}

function msgCard(m, fresh = false, opts = {}) {
    const src = String(m.source || "").toLowerCase();
    const flight = String(m.flight || "").trim().toUpperCase();
    let tail = String(m.tail || "").trim().toUpperCase();
    if (tail === "N/A") tail = "";
    const airline = airlineFromFlight(flight);
    const text = msgText(m);
    const verified = m.distance !== undefined && m.distance !== null;
    const ts = num(m.timestamp);

    const chips = [];
    if (verified) {
        const hex = m.matched_hex || m.hex || "";
        chips.push(`<span class="chip ok" data-focus="${esc(hex)}" title="Show on map">&#10003; ${Number(m.distance).toFixed(1)} mi${m.cardinal ? " " + esc(m.cardinal) : ""}</span>`);
    }
    if (m.route) chips.push(routeChip(m.route));
    if (m.label) chips.push(chip("Label", m.label + (m.label_name ? " · " + m.label_name : "")));
    if (m.block_id) chips.push(chip("Blk", m.block_id));
    if (num(m.pos_lat) !== null && num(m.pos_lon) !== null) {
        const where = num(m.pos_distance) !== null
            ? `${Math.round(m.pos_distance)} mi ${m.pos_cardinal || ""}`.trim()
            : `${Number(m.pos_lat).toFixed(3)}, ${Number(m.pos_lon).toFixed(3)}`;
        chips.push(m.pos_key
            ? `<span class="chip pos" data-pos="${esc(m.pos_key)}" title="Show reported position on map">&#9670; ${esc(where)}</span>`
            : chip("Pos", where));
    }
    if (num(m.parsed_alt_ft) !== null) chips.push(chip("Alt", `${m.parsed_alt_ft.toLocaleString()} ft`));
    if (m.parsed_route) chips.push(chip("Route", m.parsed_route));
    if (num(m.parsed_oat_c) !== null) chips.push(chip("OAT", `${m.parsed_oat_c}°C`));
    if (m.parsed_ground_station) chips.push(chip("GS", `${m.parsed_ground_station}${m.parsed_iata ? " (" + m.parsed_iata + ")" : ""}`));
    if (m.parsed_network) chips.push(chip("Net", `${m.parsed_network}${num(m.parsed_version) !== null ? " v" + m.parsed_version : ""}`));
    if (num(m.parsed_vdl_freq_mhz) !== null) chips.push(chip("VDL", `${m.parsed_vdl_freq_mhz.toFixed(3)} MHz`));

    const subParts = [airline, m.msg_type, m.hex ? "hex " + String(m.hex).toUpperCase() : ""].filter(Boolean);

    const star = opts.star && m.aid
        ? `<button class="star ${m.starred ? "on" : ""}" data-star="${esc(m.aid)}" title="${m.starred ? "Starred — kept when alerts are reset (click to unstar)" : "Star to keep this alert when alerts are reset"}" aria-label="${m.starred ? "Unstar" : "Star"} alert">${m.starred ? "&#9733;" : "&#9734;"}</button>`
        : "";
    return `<article class="msg s-${esc(src)} ${verified ? "verified" : ""} ${m.alert ? "alert" : ""} ${opts.star && m.starred ? "starred" : ""} ${fresh ? "enter" : ""}">
        <div class="m-head">
            ${avatar(airline, flight || tail)}
            <div class="m-id">
                <div class="m-flight ${flight || tail ? "tl-link" : ""}" ${flight || tail ? `data-tl="1" data-tl-flight="${esc(flight)}" data-tl-tail="${esc(tail)}" data-tl-hex="${esc(m.matched_hex || m.hex || "")}" title="Open flight timeline"` : ""}>${flight ? esc(flight) : '<span class="na">no flight</span>'}${tail ? `<span class="m-tail">${esc(tail)}</span>` : ""}</div>
                <div class="m-sub">${esc(subParts.join(" · ")) || "&nbsp;"}</div>
            </div>
            <div class="m-meta">
                <div class="m-meta-top"><span class="src-badge">${esc(src.toUpperCase() || "RADIO")}</span>${star}</div>
                <div class="m-time">${ts ? `<span data-ts="${ts}" title="${esc(new Date(ts * 1000).toLocaleString())}">${timeAgo(ts)}</span>` : ""}${num(m.freq) !== null ? " · " + Number(m.freq).toFixed(3) : ""}</div>
            </div>
        </div>
        ${m.decoded ? `<div class="m-dec">${highlight(m.decoded)}</div>` : ""}
        ${text ? `<pre class="m-text ${m.decoded ? "raw" : ""}" title="Click to expand">${highlight(text)}</pre>` : ""}
        ${chips.length ? `<div class="chips">${chips.join("")}</div>` : ""}
    </article>`;
}

function msgMatches(m) {
    const src = String(m.source || "").toLowerCase();
    if (S.hideNoise && m.noise && !m.alert) return false;
    switch (S.filter) {
        case "acars": if (src !== "acars") return false; break;
        case "vdlm2": if (src !== "vdlm2") return false; break;
        case "verified": if (m.distance === undefined || m.distance === null) return false; break;
        case "alerts": if (!m.alert) return false; break;
    }
    const q = S.q.trim().toLowerCase();
    if (q) {
        const r = m.route;
        const hay = [m.flight, m.tail, m.hex, m.label, m.label_name, m.msg_type, m.decoded, msgText(m), airlineFromFlight(m.flight),
            r ? [r.orig, r.dest, r.o_iata, r.d_iata, r.o_city, r.d_city].join(" ") : ""].join(" ").toLowerCase();
        if (!hay.includes(q)) return false;
    }
    return true;
}

function renderFeed() {
    const list = S.messages.filter(msgMatches);
    $("feed-count").textContent = `${list.length} shown`;
    $("feed").innerHTML = list.length
        ? list.slice(0, FEED_DOM_LIMIT).map(m => msgCard(m)).join("")
        : `<div class="empty">${S.messages.length ? "No messages match this filter." : "Waiting for ACARS / VDLM2 traffic&hellip;"}</div>`;
    S.pending = 0;
    renderPending();
}

function renderPending() {
    const b = $("pending");
    b.classList.toggle("show", S.paused && S.pending > 0);
    b.textContent = `${S.pending} new message${S.pending === 1 ? "" : "s"} — click to resume`;
    $("pause").classList.toggle("on", S.paused);
    $("pause").innerHTML = S.paused ? "&#9654; Resume" : "&#10074;&#10074; Pause";
}

function renderAlerts() {
    const starred = S.alerts.filter(m => m.starred).length;
    $("alerts-count").textContent = `${S.alerts.length} stored${starred ? ` · ${starred} starred` : ""}`;
    $("alert-feed").innerHTML = S.alerts.length
        ? S.alerts.map(m => msgCard(m, false, { star: true })).join("")
        : `<div class="empty" style="grid-column: 1 / -1">No alert messages yet.</div>`;
}

function toggleStar(aid) {
    const m = S.alerts.find(a => a.aid === aid);
    if (!m) return;
    m.starred = !m.starred;            // update right away; the server confirms to every open browser
    renderAlerts();
    if (ws && ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify({ type: "alert_star", aid, starred: m.starred }));
    else toast({ kind: "info", title: "NOT SAVED", main: "Dashboard offline", detail: "Reconnect and try again." });
}

let resetArm = null;
function resetAlertsClick() {
    const btn = $("alerts-reset");
    if (!resetArm) {
        // Two-step confirm (no browser pop-up): first click arms, second click within 4 s resets.
        const keep = S.alerts.filter(m => m.starred).length;
        btn.classList.add("confirm");
        btn.textContent = `Click again to delete ${S.alerts.length - keep}${keep ? ` (keeps ${keep} ★)` : ""}`;
        resetArm = setTimeout(() => { resetArm = null; btn.classList.remove("confirm"); btn.textContent = "Reset alerts"; }, 4000);
        return;
    }
    clearTimeout(resetArm);
    resetArm = null;
    btn.classList.remove("confirm");
    btn.textContent = "Reset alerts";
    if (ws && ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify({ type: "alerts_reset" }));
    else toast({ kind: "info", title: "NOT RESET", main: "Dashboard offline", detail: "Reconnect and try again." });
}

function updateAlertBadge() {
    $("b-alerts").textContent = S.unseenAlerts || S.alerts.length;
    document.querySelector('.tab[data-tab="alerts"]').classList.toggle("hot", S.unseenAlerts > 0);
}

function addMessage(m) {
    S.messages.unshift(m);
    if (S.messages.length > MAX_FEED) S.messages.length = MAX_FEED;

    if (m.alert) {
        S.alerts.unshift(m);
        if (S.alerts.length > MAX_ALERTS) {
            // trim the oldest unstarred alerts, never starred ones
            let extra = S.alerts.length - MAX_ALERTS;
            for (let i = S.alerts.length - 1; i >= 0 && extra > 0; i--) {
                if (!S.alerts[i].starred) { S.alerts.splice(i, 1); extra--; }
            }
        }
        if (S.tab !== "alerts") S.unseenAlerts++;
        renderAlerts();
        updateAlertBadge();
        toast({ kind: "alert", title: "ALERT MESSAGE", main: String(m.flight || m.tail || "Unknown").toUpperCase(), detail: msgText(m).slice(0, 80) });
    }

    if (!msgMatches(m)) return;
    if (S.paused) {
        S.pending++;
        renderPending();
        return;
    }

    const feed = $("feed");
    const empty = feed.querySelector(".empty");
    if (empty) empty.remove();
    feed.insertAdjacentHTML("afterbegin", msgCard(m, true));
    while (feed.children.length > FEED_DOM_LIMIT) feed.lastElementChild.remove();
    $("feed-count").textContent = `${S.messages.filter(msgMatches).length} shown`;
}

/* ---------- Status panels ---------- */
function renderDist(bins) {
    const max = Math.max(1, ...bins);
    $("dist").innerHTML = bins.map(c => `
        <div class="b">
            <span class="c">${c.toLocaleString()}</span>
            <div class="bar" style="height:${Math.max(2, c / max * 100)}%"></div>
        </div>`).join("");
}

function renderFreqs(counts) {
    const entries = Object.entries(counts || {}).map(([f, c]) => [Number(f), c]).filter(([f]) => Number.isFinite(f));
    $("freq-count").textContent = `${entries.length} active`;
    if (!entries.length) {
        $("freqs").innerHTML = '<div class="na" style="font-size:12px">No frequencies yet.</div>';
        return;
    }
    entries.sort((a, b) => b[1] - a[1]);
    const max = entries[0][1];
    $("freqs").innerHTML = entries.slice(0, 12).map(([f, c]) => {
        // VDL2 lives at 136.x MHz; everything else is classic ACARS.
        const vdl = f >= 136 && f < 137;
        return `<div class="freq-row ${vdl ? "vdl" : ""}">
            <span class="f">${f.toFixed(3)}</span>
            <span class="track"><div style="width:${c / max * 100}%"></div></span>
            <span class="n">${c.toLocaleString()}</span>
        </div>`;
    }).join("");
}

function renderAirlines(counts) {
    const entries = Object.entries(counts || {}).sort((a, b) => b[1] - a[1]);
    if (!entries.length) {
        $("airlines").innerHTML = '<div class="na" style="font-size:12px">No airline traffic yet.</div>';
        return;
    }
    const max = entries[0][1];
    $("airlines").innerHTML = entries.slice(0, 10).map(([name, c], i) => {
        const changed = S.prevAirlines.size && S.prevAirlines.get(name) !== c;
        return `<div class="al-row ${changed ? "flash" : ""}">
            <span class="rk">${i + 1}</span>
            ${avatar(name, name)}
            <span class="nm">${esc(name)}<div class="track"><div style="width:${c / max * 100}%"></div></div></span>
            <span class="ct">${c.toLocaleString()}</span>
        </div>`;
    }).join("");
    S.prevAirlines = new Map(entries);
}

function renderWatch(list) {
    S.watch = list || [];
    const box = $("watch");
    if (!S.watch.length) {
        box.hidden = true;
        return;
    }
    box.hidden = false;
    $("watch-items").innerHTML = S.watch.map(w => {
        const ident = String(w.flight || w.reg || w.hex || "").toUpperCase();
        const isNew = !S.watchSeen.has(w.hex);
        if (isNew) {
            S.watchSeen.add(w.hex);
            toast({ kind: "watch", title: "TRACKED AIRCRAFT", main: ident, detail: `${w.owner ? w.owner + " · " : ""}~${Math.round(w.distance)} mi ${w.cardinal || ""}`, hex: w.hex });
        }
        const href = `https://globe.adsbexchange.com/?icao=${encodeURIComponent(String(w.hex || "").toLowerCase())}`;
        return `<a class="w-item ${isNew ? "fresh" : ""}" href="${href}" target="_blank" rel="noopener">
            <b>${esc(ident)}</b>
            ${w.tail && w.tail !== ident ? `<span>${esc(w.tail)}</span>` : ""}
            ${w.owner ? `<span>${esc(w.owner)}</span>` : ""}
            <span>~${Math.round(w.distance)} mi ${esc(w.cardinal || "")}</span>
        </a>`;
    }).join("");
}

function onStatus(p) {
    S.status = p;
    light("acars", p.acars);
    light("vdlm2", p.vdlm2);
    if (typeof p.adsb === "boolean") light("adsb", p.adsb);
    if (p.uptime) $("uptime").textContent = p.uptime;

    const total = p.total_messages || 0;
    const matched = p.matched_messages || 0;
    setNum("k-total", total.toLocaleString());
    setNum("k-verified", matched.toLocaleString());
    const pct = total ? matched / total * 100 : 0;
    $("k-verified-m").style.width = pct.toFixed(1) + "%";
    $("k-verified-h").textContent = `${pct.toFixed(1)}% matched to ADS-B`;

    const radioMin = (p.total_radio_rate || 0) * 60;
    $("k-radio").textContent = radioMin.toFixed(1);
    $("k-radio-h").textContent = `ACARS ${((p.acars_rate || 0) * 60).toFixed(1)} · VDLM2 ${((p.vdlm2_rate || 0) * 60).toFixed(1)}`;
    $("k-total-h").textContent = `${radioMin.toFixed(1)} per minute right now`;
    $("k-aircraft-h").textContent = `${Math.round(p.adsb_rate || 0).toLocaleString()} msg/s`;
    setNum("k-alerts", (p.alert_count ?? S.alerts.length).toLocaleString());

    // Sample sparklines at most every 4s (status also arrives with each message).
    if (Date.now() - S.lastSpark > 4000) {
        S.lastSpark = Date.now();
        S.radioHist.push(radioMin);
        S.adsbHist.push(p.adsb_rate || 0);
        if (S.radioHist.length > 72) S.radioHist.shift();
        if (S.adsbHist.length > 72) S.adsbHist.shift();
        sparkline("spark-radio", S.radioHist, "#fbbf24");
        sparkline("spark-adsb", S.adsbHist, "#38bdf8");
    }

    if (p.distance_bins) renderDist(p.distance_bins);
    if (p.freq_counts) renderFreqs(p.freq_counts);
    if (p.airline_counts) renderAirlines(p.airline_counts);
    if (Array.isArray(p.verified_hexes)) S.verified = new Set(p.verified_hexes.map(h => String(h || "").toLowerCase()));
    renderWatch(Array.isArray(p.watch_list) ? p.watch_list : (p.watch ? [p.watch] : []));
    if (Array.isArray(p.alert_terms)) setTerms(p.alert_terms);

    $("foot-left").textContent = `Server time ${new Date((p.server_time || Date.now() / 1000) * 1000).toLocaleTimeString()} · ${total.toLocaleString()} messages since tracking began`;
}

/* ---------- Toasts ---------- */
const recentToasts = new Map();
function toast({ kind, title, main, detail, hex, airline }) {
    // Collapse repeats of the same event (e.g. a message received twice) within 20s.
    const key = `${kind}|${main}`;
    const now = Date.now();
    if (now - (recentToasts.get(key) || 0) < 20000) return;
    recentToasts.set(key, now);

    const colors = { verified: "#22e584", alert: "#f43f5e", watch: "#22e584", emg: "#ef4444" };
    const box = $("toasts");
    const t = document.createElement("div");
    t.className = "toast";
    t.style.setProperty("--c", colors[kind] || "#38bdf8");
    t.innerHTML = `${avatar(airline, main)}<div style="min-width:0">
        <div class="tt">${esc(title)}</div>
        <div class="tc">${esc(main)}</div>
        <div class="td">${esc(detail || "")}</div>
    </div>`;
    if (hex) t.addEventListener("click", () => focusPlane(hex));
    else if (kind === "alert") t.addEventListener("click", () => setTab("alerts"));
    box.append(t);
    while (box.children.length > 3) box.firstElementChild.remove();
    setTimeout(() => {
        t.classList.add("out");
        setTimeout(() => t.remove(), 400);
    }, 7000);
}

/* ---------- ADS-B ---------- */
function renderAircraftList() {
    const rows = S.aircraft
        .filter(ac => num(ac.lat) !== null && num(ac.lon) !== null)
        .map(ac => ({ ac, d: distMiles(HOME_LAT, HOME_LON, ac.lat, ac.lon), b: bearing(HOME_LAT, HOME_LON, ac.lat, ac.lon) }))
        .sort((a, b) => a.d - b.d);

    $("ac-count").textContent = `${rows.length} with position · nearest first`;

    $("ac-list").innerHTML = rows.slice(0, 60).map(({ ac, d, b }) => {
        const hex = String(ac.hex || "").toLowerCase();
        const flight = String(ac.flight || "").trim().toUpperCase();
        const airline = airlineFromFlight(flight);
        const alt = ac.alt_baro === "ground" ? "GND" : (altOf(ac) !== null ? altOf(ac).toLocaleString() + " ft" : "—");
        const vr = num(ac.baro_rate ?? ac.geom_rate);
        const arrow = vr === null ? "" : vr > 300 ? ' <span class="up">↑</span>' : vr < -300 ? ' <span class="down">↓</span>' : "";
        const gs = num(ac.gs);
        return `<div class="ac-row ${S.verified.has(hex) ? "ver" : ""}" data-focus="${esc(hex)}" title="Show on map">
            ${acAvatar(ac, airline, identOf(ac))}
            <div style="min-width:0">
                <div class="id">${esc(identOf(ac))}${ac.t ? `<span class="t">${esc(ac.t)}</span>` : ""}${isHeli(ac) ? '<span class="heli-tag">HELI</span>' : ""}${apBadge(S.events[hex])}${S.emerg[hex] && S.emerg[hex].active ? `<span class="sq-tag" title="${esc(S.emerg[hex].desc)}">${esc(S.emerg[hex].code || "EMERG")}</span>` : ""}</div>
                <div class="meta">${alt}${arrow}${gs !== null ? " · " + Math.round(gs) + " kt" : ""}${S.routes[hex] ? ` · <span class="rt-inline" title="${esc(rtLong(S.routes[hex]))}">${esc(rtShort(S.routes[hex]))}</span>` : (airline ? " · " + esc(airline) : "")}</div>
            </div>
            <div class="dd">${d.toFixed(1)} mi<small>${cardinal(b)}</small></div>
        </div>`;
    }).join("") || '<div class="empty">No ADS-B aircraft with positions.</div>';
}

function compassSvg(brg) {
    return `<svg viewBox="0 0 74 74">
        <circle cx="37" cy="37" r="33" fill="rgba(34,229,132,0.05)" stroke="rgba(34,229,132,0.35)" stroke-width="1.5"/>
        <circle cx="37" cy="37" r="22" fill="none" stroke="rgba(34,229,132,0.12)"/>
        <text x="37" y="11" text-anchor="middle" font-size="8" fill="#8696ab" font-family="JetBrains Mono, monospace">N</text>
        <g transform="rotate(${brg.toFixed(0)} 37 37)">
            <path d="M37 6 L42 17 L37 14.5 L32 17 Z" fill="#22e584"/>
        </g>
    </svg>`;
}

function renderNearby() {
    const rows = [];
    for (const ac of S.aircraft) {
        if (num(ac.lat) === null || num(ac.lon) === null) continue;
        const alt = num(ac.alt_baro ?? ac.alt_geom);
        if (alt === null || alt >= NEAR_ALT) continue;
        const d = distMiles(HOME_LAT, HOME_LON, ac.lat, ac.lon);
        if (!(d <= NEAR_MILES)) continue;
        rows.push({ ac, d, b: bearing(HOME_LAT, HOME_LON, ac.lat, ac.lon), alt });
    }
    rows.sort((a, b) => a.d - b.d);

    setNum("k-nearby", rows.length);
    $("b-nearby").textContent = rows.length;
    document.querySelector('.tab[data-tab="nearby"]').classList.toggle("hot", rows.length > 0 && S.tab !== "nearby");

    $("nearby").innerHTML = rows.map(({ ac, d, b, alt }) => {
        const flight = String(ac.flight || "").trim().toUpperCase();
        const airline = airlineFromFlight(flight);
        const vr = num(ac.baro_rate ?? ac.geom_rate);
        const gs = num(ac.gs);
        const reg = String(ac.r || "").toUpperCase();
        return `<div class="near" data-focus="${esc(String(ac.hex || "").toLowerCase())}">
            <div class="compass">${compassSvg(b)}<div class="cd">${cardinal(b)}</div></div>
            <div class="info">
                <div class="nid">${acAvatar(ac, airline, identOf(ac))}<div style="min-width:0">
                    <div class="big">${esc(identOf(ac))}${isHeli(ac) ? '<span class="heli-tag">HELI</span>' : ""}</div>
                    <div class="s">${esc([airline, reg && reg !== identOf(ac) ? reg : "", ac.t, isHeli(ac) ? "Helicopter" : ""].filter(Boolean).join(" · ")) || "&nbsp;"}</div>
                </div></div>
                <div class="nums">
                    <div><div class="k">Dist</div><div class="v">${d.toFixed(1)} mi</div></div>
                    <div><div class="k">Alt</div><div class="v ${vr > 300 ? "up" : vr < -300 ? "down" : ""}">${Math.round(alt).toLocaleString()}${vr > 300 ? "↑" : vr < -300 ? "↓" : ""}</div></div>
                    <div><div class="k">Speed</div><div class="v">${gs !== null ? Math.round(gs) + " kt" : "—"}</div></div>
                </div>
            </div>
        </div>`;
    }).join("") || `<div class="empty" style="grid-column: 1 / -1">No aircraft within ${NEAR_MILES} mi below ${NEAR_ALT.toLocaleString()} ft right now.</div>`;
}

async function fetchAdsb() {
    try {
        const res = await fetch("/aircraft.json", { cache: "no-store" });
        if (!res.ok) throw new Error("HTTP " + res.status);
        const json = await res.json();
        S.aircraft = json.aircraft || [];
        S.routes = json.routes || {};
        S.rejects = json.route_rejects || {};
        S.events = json.events || {};
        S.emerg = json.emergencies || {};
        light("adsb", true);
    } catch (e) {
        S.aircraft = [];
        S.routes = {};
        S.events = {};
        S.emerg = {};
        light("adsb", false);
    }
    S.acByHex = new Map(S.aircraft.map(ac => [String(ac.hex || "").toLowerCase(), ac]));
    S.adsbRegs = new Set(S.aircraft.map(ac => normReg(ac.r || ac.reg)).filter(r => r.length >= 3));
    S.adsbFlights = new Set(S.aircraft.map(ac => String(ac.flight || "").replace(/[^A-Za-z0-9]/g, "").toUpperCase()).filter(f => f.length >= 3));
    await fetchPositions();
    renderEmerg();
    setNum("k-aircraft", S.aircraft.length);
    renderAircraftList();
    renderNearby();
    updateMap();
}

/* ---------- Map ---------- */
const PLANE_PATH = "M12 1.5c.9 0 1.5.8 1.5 1.7v5.6l8 4.8v2.2l-8-2.5v5l2.4 1.8v1.6L12 20.6l-3.9 1.1v-1.6l2.4-1.8v-5l-8 2.5v-2.2l8-4.8V3.2c0-.9.6-1.7 1.5-1.7z";
let map = null;
let planeLayer = null;
const markers = new Map();
let mapFitted = false;

function altColor(ac) {
    if (ac.alt_baro === "ground") return "#94a3b8";
    const a = altOf(ac);
    if (a === null) return "#94a3b8";
    if (a < 10000) return "#38bdf8";
    if (a < 25000) return "#a78bfa";
    return "#fbbf24";
}

function initMap() {
    if (!window.L) {
        $("map").innerHTML = '<div class="empty" style="margin:20px">Map unavailable (could not load Leaflet).</div>';
        return;
    }
    map = L.map("map", { worldCopyJump: true }).setView([HOME_LAT, HOME_LON], 7);
    L.tileLayer("https://tile.openstreetmap.org/{z}/{x}/{y}.png", {
        maxZoom: 18,
        className: "dark-tiles",
        attribution: '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors',
    }).addTo(map);

    [25, 50, 100, 200].forEach(mi => {
        L.circle([HOME_LAT, HOME_LON], { radius: mi * 1609.34, color: "#22e584", opacity: 0.35, weight: 1, dashArray: "4 6", fill: false, interactive: false }).addTo(map);
        const lat = HOME_LAT + mi / 69.0;
        L.marker([lat, HOME_LON], { interactive: false, icon: L.divIcon({ className: "", html: `<span class="ring-lbl">${mi} mi</span>`, iconSize: [40, 12], iconAnchor: [-4, 6] }) }).addTo(map);
    });

    L.circleMarker([HOME_LAT, HOME_LON], { radius: 6, color: "#fff", weight: 2, fillColor: "#22e584", fillOpacity: 1 })
        .bindTooltip("Home station", { direction: "top" }).addTo(map);

    trailLayer = L.layerGroup().addTo(map);
    routeLayer = L.layerGroup().addTo(map);
    planeLayer = L.layerGroup().addTo(map);
    posLayer = L.layerGroup().addTo(map);

    map.on("popupopen", e => {
        const src = e.popup && e.popup._source;
        if (src && src._hex) selectTrack({ hex: src._hex });
        else if (src && src._key) selectTrack({ key: src._key });
    });
    map.on("popupclose", e => {
        const src = e.popup && e.popup._source;
        if (!S.sel || !src) return;
        if ((S.sel.hex && S.sel.hex === src._hex) || (S.sel.key && S.sel.key === src._key)) clearTrack();
    });
}

function planeHtml(ac, hex) {
    const ver = S.verified.has(hex);
    const watched = S.watch.some(w => String(w.hex || "").toLowerCase() === hex);
    const trk = num(ac.track ?? ac.true_heading ?? ac.mag_heading) ?? 0;
    const label = S.labels ? `<span class="pl-lbl">${esc(identOf(ac))}</span>` : "";
    const shape = isHeli(ac) ? HELI_SVG_INNER : `<path d="${PLANE_PATH}"/>`;
    const emg = S.emerg[hex] && S.emerg[hex].active;
    return `<div class="pl ${ver ? "ver" : ""} ${watched ? "trk" : ""} ${emg ? "emg" : ""}" style="--c:${altColor(ac)}"><svg viewBox="0 0 24 24" style="transform:rotate(${Math.round(trk)}deg)">${shape}</svg>${label}</div>`;
}

function popupHtml(hex) {
    const ac = S.acByHex.get(hex);
    if (!ac) return "<i>Aircraft no longer tracked</i>";
    const flight = String(ac.flight || "").trim().toUpperCase();
    const airline = airlineFromFlight(flight);
    const d = distMiles(HOME_LAT, HOME_LON, ac.lat, ac.lon);
    const b = bearing(HOME_LAT, HOME_LON, ac.lat, ac.lon);
    const vr = num(ac.baro_rate ?? ac.geom_rate);
    const rows = [
        ["Altitude", ac.alt_baro === "ground" ? "Ground" : (altOf(ac) !== null ? altOf(ac).toLocaleString() + " ft" : "—")],
        vr !== null ? ["Vertical", (vr > 0 ? "+" : "") + Math.round(vr) + " fpm"] : null,
        num(ac.gs) !== null ? ["Speed", Math.round(ac.gs) + " kt"] : null,
        num(ac.track) !== null ? ["Track", String(Math.round(ac.track)).padStart(3, "0") + "°"] : null,
        ["From home", `${d.toFixed(1)} mi ${cardinal(b)}`],
        ac.squawk ? ["Squawk", ac.squawk + (S.emerg[hex] ? " ⚠" : "")] : null,
        ac.r ? ["Reg", ac.r] : null,
        (ac.t || isHeli(ac)) ? ["Type", [ac.t, isHeli(ac) ? "Helicopter" : ""].filter(Boolean).join(" · ")] : null,
    ].filter(Boolean);
    return `<div class="pop-id">${esc(identOf(ac))}</div>
        <div class="pop-sub">${esc([airline, "hex " + hex.toUpperCase()].filter(Boolean).join(" · "))}</div>
        ${S.emerg[hex] ? `<div class="pop-emg">&#9888; ${esc(S.emerg[hex].desc)}${S.emerg[hex].code ? " · squawk " + esc(S.emerg[hex].code) : ""}${S.emerg[hex].active ? "" : " (cleared)"}</div>` : ""}
        ${S.routes[hex] ? routePopupBlock(S.routes[hex]) : (S.rejects && S.rejects[hex] ? `<div class="pop-rsrc">Route unknown &mdash; database says ${esc(S.rejects[hex])}, which doesn't match this flight's position</div>` : "")}
        ${rows.map(([k, v]) => `<div class="pop-row"><span>${esc(k)}</span><span>${esc(v)}</span></div>`).join("")}
        ${S.verified.has(hex) ? '<div class="pop-ver">&#10003; Recent radio message verified</div>' : ""}
        <div style="margin-top:8px;display:flex;gap:12px;flex-wrap:wrap"><a href="#" data-tl="1" data-tl-hex="${esc(hex)}">Flight timeline &rsaquo;</a><a href="https://globe.adsbexchange.com/?icao=${encodeURIComponent(hex)}" target="_blank" rel="noopener">ADS-B Exchange &#8599;</a></div>`;
}

function updateMap() {
    if (!map) return;
    const live = new Set();
    let plotted = 0;

    for (const ac of S.aircraft) {
        const lat = num(ac.lat), lon = num(ac.lon);
        if (lat === null || lon === null) continue;
        const hex = String(ac.hex || "").toLowerCase();
        if (!hex) continue;
        live.add(hex);
        plotted++;

        const html = planeHtml(ac, hex);
        const big = S.verified.has(hex);
        let m = markers.get(hex);
        if (!m) {
            m = L.marker([lat, lon], { icon: L.divIcon({ className: "", html, iconSize: big ? [28, 28] : [22, 22], iconAnchor: big ? [14, 14] : [11, 11] }) });
            m._html = html;
            m._hex = hex;
            m.bindPopup(() => popupHtml(hex));
            planeLayer.addLayer(m);
            markers.set(hex, m);
        } else {
            m.setLatLng([lat, lon]);
            if (m._html !== html) {
                m._html = html;
                m.setIcon(L.divIcon({ className: "", html, iconSize: big ? [28, 28] : [22, 22], iconAnchor: big ? [14, 14] : [11, 11] }));
            }
            if (m.isPopupOpen()) m.setPopupContent(popupHtml(hex));
        }
    }

    for (const [hex, m] of markers) {
        if (!live.has(hex)) {
            planeLayer.removeLayer(m);
            markers.delete(hex);
        }
    }

    const radioOnly = updatePositions();
    if (S.sel && Date.now() - (S.sel.fetched || 0) > 5000) refreshTrack();
    const helis = S.aircraft.filter(ac => num(ac.lat) !== null && isHeli(ac)).length;
    $("m-count").textContent = `${plotted} aircraft plotted${helis ? ` · ${helis} helicopter${helis === 1 ? "" : "s"}` : ""}${radioOnly ? ` · ${radioOnly} radio-only` : ""}`;

    if (!mapFitted && plotted && S.tab === "map") {
        fitMap();
        mapFitted = true;
    }
}

function fitMap() {
    if (!map) return;
    const pts = [[HOME_LAT, HOME_LON]];
    for (const m of [...markers.values(), ...posMarkers.values()]) {
        const ll = m.getLatLng();
        pts.push([ll.lat, ll.lng]);
    }
    if (pts.length > 1) map.fitBounds(pts, { padding: [30, 30], maxZoom: 10 });
}

function focusPlane(hex) {
    hex = String(hex || "").toLowerCase();
    setTab("map");
    setTimeout(() => {
        const m = markers.get(hex);
        if (!m || !map) return;
        mapFitted = true;
        map.flyTo(m.getLatLng(), Math.max(map.getZoom(), 9), { duration: 0.8 });
        setTimeout(() => m.openPopup(), 850);
    }, 120);
}

/* ---------- Routes & trails on the map ---------- */
let routeLayer = null;
let trailLayer = null;
let trailsTimer = null;

function gcPoints(a, b, n = 48) {
    // Great-circle path between [lat, lon] pairs (looks right on a Mercator map).
    const toR = d => d * Math.PI / 180, toD = r => r * 180 / Math.PI;
    const [la1, lo1, la2, lo2] = [toR(a[0]), toR(a[1]), toR(b[0]), toR(b[1])];
    const d = 2 * Math.asin(Math.sqrt(Math.sin((la2 - la1) / 2) ** 2 + Math.cos(la1) * Math.cos(la2) * Math.sin((lo2 - lo1) / 2) ** 2));
    if (!isFinite(d) || d < 1e-6) return [a, b];
    const pts = [];
    for (let i = 0; i <= n; i++) {
        const f = i / n;
        const A = Math.sin((1 - f) * d) / Math.sin(d), B = Math.sin(f * d) / Math.sin(d);
        const x = A * Math.cos(la1) * Math.cos(lo1) + B * Math.cos(la2) * Math.cos(lo2);
        const y = A * Math.cos(la1) * Math.sin(lo1) + B * Math.cos(la2) * Math.sin(lo2);
        const z = A * Math.sin(la1) + B * Math.sin(la2);
        pts.push([toD(Math.atan2(z, Math.sqrt(x * x + y * y))), toD(Math.atan2(y, x))]);
    }
    return pts;
}

function airportMarker(code, name, lat, lon) {
    return L.marker([lat, lon], {
        interactive: true,
        icon: L.divIcon({ className: "", html: `<span class="ap-lbl">${esc(code)}</span>`, iconSize: [0, 0] }),
    }).bindTooltip(esc(name || code), { direction: "top", offset: [0, -10] });
}

function trailColor(alt) {
    if (alt === 0) return "#94a3b8";
    if (alt === null || alt === undefined) return "#cbd5e1";
    if (alt < 10000) return "#38bdf8";
    if (alt < 25000) return "#a78bfa";
    return "#fbbf24";
}

function drawTrack(t) {
    if (!routeLayer) return;
    routeLayer.clearLayers();
    if (!t) return;
    const r = t.route;
    const pos = t.pos;

    // Flown path, coloured by altitude like the plane icons
    const tr = t.trail || [];
    if (tr.length >= 2) {
        let seg = [[tr[0][0], tr[0][1]]], col = trailColor(tr[0][2]);
        for (let i = 1; i < tr.length; i++) {
            const c = trailColor(tr[i][2]);
            seg.push([tr[i][0], tr[i][1]]);
            if (c !== col || i === tr.length - 1) {
                L.polyline(seg, { color: col, weight: 3, opacity: 0.95, interactive: false }).addTo(routeLayer);
                seg = [[tr[i][0], tr[i][1]]];
                col = c;
            }
        }
        if (pos) L.polyline([[tr[tr.length - 1][0], tr[tr.length - 1][1]], pos], { color: col, weight: 3, opacity: 0.95, interactive: false }).addTo(routeLayer);
    }

    if (!r) return;
    const hasO = num(r.o_lat) !== null && num(r.o_lon) !== null;
    const hasD = num(r.d_lat) !== null && num(r.d_lon) !== null;
    const o = hasO ? [r.o_lat, r.o_lon] : null;
    const d = hasD ? [r.d_lat, r.d_lon] : null;
    const start = tr.length ? [tr[0][0], tr[0][1]] : pos;
    const lineStyle = { color: "#e8eef6", weight: 1.5, opacity: 0.55, interactive: false };
    const dashStyle = { color: "#9fb0c8", weight: 2, opacity: 0.85, dashArray: "6 7", interactive: false };

    if (o && start) L.polyline(gcPoints(o, start), lineStyle).addTo(routeLayer);
    if (d && pos) L.polyline(gcPoints(pos, d), dashStyle).addTo(routeLayer);
    else if (o && d && !pos) L.polyline(gcPoints(o, d), dashStyle).addTo(routeLayer);
    if (o) airportMarker(r.o_iata || r.orig, `${r.o_name || r.orig} — origin`, o[0], o[1]).addTo(routeLayer);
    if (d) airportMarker(r.d_iata || r.dest, `${r.d_name || r.dest} — destination`, d[0], d[1]).addTo(routeLayer);
}

async function refreshTrack() {
    const sel = S.sel;
    if (!sel) return;
    sel.fetched = Date.now();
    try {
        const q = sel.hex ? "hex=" + encodeURIComponent(sel.hex) : "key=" + encodeURIComponent(sel.key);
        const res = await fetch("/api/track?" + q, { cache: "no-store" });
        const t = await res.json();
        if (S.sel !== sel) return;      // selection changed while loading
        drawTrack(t);
    } catch (e) {}
}

function selectTrack(sel) {
    S.sel = sel;
    if (routeLayer) routeLayer.clearLayers();
    refreshTrack();
}

function clearTrack() {
    S.sel = null;
    if (routeLayer) routeLayer.clearLayers();
}

async function loadAllTrails() {
    if (!trailLayer) return;
    try {
        const res = await fetch("/api/trails", { cache: "no-store" });
        const j = await res.json();
        trailLayer.clearLayers();
        if (!S.showTrails) return;
        for (const [hex, pts] of Object.entries(j.trails || {})) {
            if (S.sel && S.sel.hex === hex) continue;  // the selected plane gets the detailed trail
            const ac = S.acByHex.get(hex);
            const line = ac && num(ac.lat) !== null ? [...pts, [ac.lat, ac.lon]] : pts;
            L.polyline(line, { color: ac ? altColor(ac) : "#94a3b8", weight: 1.5, opacity: 0.45, interactive: false }).addTo(trailLayer);
        }
    } catch (e) {}
}

function setTrails(on) {
    S.showTrails = on;
    $("m-trails").classList.toggle("on", on);
    clearInterval(trailsTimer);
    if (on) {
        loadAllTrails();
        trailsTimer = setInterval(loadAllTrails, 10000);
    } else if (trailLayer) {
        trailLayer.clearLayers();
    }
    try { localStorage.setItem("avdash-trails", on ? "1" : "0"); } catch (e) {}
}

/* ---------- Airport events ---------- */
function agoShort(ts) {
    const s = Math.max(0, Date.now() / 1000 - ts);
    return s < 60 ? "now" : s < 3600 ? Math.floor(s / 60) + "m" : Math.floor(s / 3600) + "h";
}
function apBadge(ev) {
    if (!ev) return "";
    const dep = ev.type === "departure";
    const fresh = Date.now() / 1000 - ev.ts < 60;
    const tip = `${dep ? "Departing" : "Arriving"} ${ev.name || ev.code}` +
        (ev.vr !== null && ev.vr !== undefined ? ` · ${ev.vr > 0 ? "+" : ""}${ev.vr} fpm` : "") +
        (ev.agl !== null && ev.agl !== undefined ? ` · ${ev.agl.toLocaleString()} ft above field` : "") +
        ` · detected ${new Date(ev.ts * 1000).toLocaleTimeString([], { hour: "2-digit", minute: "2-digit" })}`;
    return `<span class="apx ${dep ? "dep" : "arr"} ${fresh ? "fresh" : ""}" title="${esc(tip)}">${dep ? "&#8599; DEP" : "&#8600; ARR"} ${esc(ev.code)} · ${agoShort(ev.ts)}</span>`;
}

/* ---------- Emergencies ---------- */
function renderEmerg() {
    const list = Object.values(S.emerg || {});
    const box = $("emg-banner");
    if (!list.length) { box.hidden = true; return; }
    box.hidden = false;
    $("emg-items").innerHTML = list.map(e => {
        const who = String(e.flight || e.reg || e.hex || "").toUpperCase();
        if (e.active && !S.emergSeen.has(e.hex + (e.code || ""))) {
            S.emergSeen.add(e.hex + (e.code || ""));
            toast({ kind: "emg", title: "EMERGENCY", main: who, detail: `${e.desc}${e.code ? " · squawk " + e.code : ""}${e.distance != null ? ` · ~${Math.round(e.distance)} mi ${e.cardinal || ""}` : ""}`, hex: e.hex });
        }
        const alt = e.alt === "ground" ? "ground" : (num(e.alt) !== null ? Number(e.alt).toLocaleString() + " ft" : "");
        return `<span class="e-item ${e.active ? "" : "cleared"}" data-focus="${esc(e.hex)}" title="Show on map">
            <b>${esc(who)}</b>${e.code ? `<span class="sq">${esc(e.code)}</span>` : ""}<span>${esc(e.desc)}${e.active ? "" : " · cleared"}</span>
            ${alt ? `<span>${esc(alt)}</span>` : ""}${e.distance != null ? `<span>~${Math.round(e.distance)} mi ${esc(e.cardinal || "")}</span>` : ""}</span>`;
    }).join("");
}

/* ---------- Coverage outlines ---------- */
let covLayer = null, covTimer = null;
const COV_COLORS = { acars: "#fbbf24", vdlm2: "#a78bfa" };

function covPolygon(rows, binDeg) {
    // rows: [bin, dist, lat, lon, ts, flight] sorted by bin. Where several bins in a row have no
    // contacts, dip back to home so the outline doesn't claim coverage it never saw.
    const pts = [];
    for (let i = 0; i < rows.length; i++) {
        const cur = rows[i], prev = rows[(i - 1 + rows.length) % rows.length];
        const gap = (cur[0] - prev[0] + 360 / binDeg) % (360 / binDeg);
        if (rows.length > 1 && gap > 3) pts.push([HOME_LAT, HOME_LON]);
        pts.push([cur[2], cur[3]]);
    }
    return pts;
}

async function loadCoverage() {
    if (!map || !S.showCov) return;
    let j;
    try { j = await (await fetch("/api/coverage", { cache: "no-store" })).json(); } catch (e) { return; }
    if (!covLayer) covLayer = L.layerGroup().addTo(map);
    covLayer.clearLayers();
    for (const mode of ["vdlm2", "acars"]) {
        const rows = j[mode] || [];
        const color = COV_COLORS[mode];
        const name = mode === "acars" ? "ACARS" : "VDLM2";
        const far = rows.reduce((b, r) => (r[1] > (b ? b[1] : 0) ? r : b), null);
        $(mode === "acars" ? "cov-lg-a-t" : "cov-lg-v-t").textContent = `${name} coverage${far ? ` · max ${Math.round(far[1])} mi` : " · no data yet"}`;
        if (rows.length >= 3) {
            L.polygon(covPolygon(rows, j.bin_deg || 5), { color, weight: 2, opacity: 0.9, fillColor: color, fillOpacity: 0.07, interactive: false }).addTo(covLayer);
        }
        for (const r of rows) {
            const when = new Date(r[4] * 1000).toLocaleDateString([], { month: "short", day: "numeric" });
            L.circleMarker([r[2], r[3]], { radius: 3, color, weight: 1, fillColor: color, fillOpacity: 0.9 })
                .bindTooltip(`${name} · ${Math.round(r[1])} mi at ${String(r[0] * (j.bin_deg || 5)).padStart(3, "0")}°${r[5] ? " · " + esc(r[5]) : ""} · ${when}`, { direction: "top" })
                .addTo(covLayer);
        }
    }
}

function setCoverage(on) {
    S.showCov = on;
    $("m-cov").classList.toggle("on", on);
    $("cov-lg-a").hidden = !on;
    $("cov-lg-v").hidden = !on;
    clearInterval(covTimer);
    if (on) { loadCoverage(); covTimer = setInterval(loadCoverage, 60000); }
    else if (covLayer) covLayer.clearLayers();
    try { localStorage.setItem("avdash-cov", on ? "1" : "0"); } catch (e) {}
}

/* ---------- Weather radar (RainViewer) ---------- */
const RADAR = { on: false, host: "", frames: [], layers: new Map(), idx: -1, loop: false, loopTimer: null, refreshTimer: null };

function radarLayer(frame) {
    let l = RADAR.layers.get(frame.path);
    if (!l) {
        l = L.tileLayer(`${RADAR.host}${frame.path}/256/{z}/{x}/{y}/2/1_1.png`, {
            opacity: 0, maxNativeZoom: 7, maxZoom: 18, zIndex: 5,
            attribution: 'Radar &copy; <a href="https://www.rainviewer.com/" target="_blank" rel="noopener">RainViewer</a>',
        });
        RADAR.layers.set(frame.path, l);
    }
    if (!map.hasLayer(l)) l.addTo(map);
    return l;
}

function radarShow(i) {
    if (!map || !RADAR.frames.length) return;
    i = (i + RADAR.frames.length) % RADAR.frames.length;
    const f = RADAR.frames[i];
    const cur = radarLayer(f);
    for (const [p, l] of RADAR.layers) {
        if (l !== cur && map.hasLayer(l)) {
            // keep other frames loaded (invisible) while looping so playback is smooth
            if (RADAR.loop) l.setOpacity(0); else map.removeLayer(l);
        }
    }
    cur.setOpacity(0.6);
    RADAR.idx = i;
    const t = new Date(f.time * 1000);
    const age = Math.round((Date.now() / 1000 - f.time) / 60);
    $("radar-info").hidden = false;
    $("radar-info").textContent = `Radar ${t.toLocaleTimeString([], { hour: "2-digit", minute: "2-digit" })}${RADAR.loop ? "" : age > 1 ? ` · ${age} min ago` : ""}`;
}

async function radarRefresh() {
    try {
        const res = await fetch("https://api.rainviewer.com/public/weather-maps.json", { cache: "no-store" });
        const j = await res.json();
        RADAR.host = j.host || "https://tilecache.rainviewer.com";
        const frames = ((j.radar || {}).past || []).filter(f => f && f.path);
        if (!frames.length) throw new Error("no frames");
        // forget layers for frames that have aged out
        const keep = new Set(frames.map(f => f.path));
        for (const [p, l] of RADAR.layers) {
            if (!keep.has(p)) { if (map.hasLayer(l)) map.removeLayer(l); RADAR.layers.delete(p); }
        }
        RADAR.frames = frames;
        if (RADAR.on && !RADAR.loop) radarShow(frames.length - 1);
    } catch (e) {
        $("radar-info").hidden = false;
        $("radar-info").textContent = "Radar unavailable";
    }
}

function radarLoop(on) {
    RADAR.loop = on;
    $("m-loop").classList.toggle("on", on);
    clearInterval(RADAR.loopTimer);
    if (on) {
        RADAR.frames.forEach(f => radarLayer(f));   // preload every frame
        let pause = 0;
        RADAR.loopTimer = setInterval(() => {
            if (RADAR.idx === RADAR.frames.length - 1 && pause++ < 3) return;   // linger on the latest frame
            pause = 0;
            radarShow(RADAR.idx + 1);
        }, 550);
    } else if (RADAR.frames.length) {
        radarShow(RADAR.frames.length - 1);
    }
}

async function setRadar(on) {
    if (!map) return;
    RADAR.on = on;
    $("m-radar").classList.toggle("on", on);
    $("m-loop").hidden = !on;
    clearInterval(RADAR.refreshTimer);
    if (on) {
        await radarRefresh();
        RADAR.refreshTimer = setInterval(radarRefresh, 5 * 60 * 1000);
    } else {
        radarLoop(false);
        for (const l of RADAR.layers.values()) if (map.hasLayer(l)) map.removeLayer(l);
        $("radar-info").hidden = true;
    }
    try { localStorage.setItem("avdash-radar", on ? "1" : "0"); } catch (e) {}
}

/* ---------- Local weather (METAR) ---------- */
const WX_CAT = { VFR: "#22c55e", MVFR: "#3b82f6", IFR: "#ef4444", LIFR: "#d946ef" };
const WX_CODES = {
    TS: "thunderstorm", RA: "rain", DZ: "drizzle", SN: "snow", SG: "snow grains", PL: "ice pellets", GR: "hail", GS: "small hail",
    UP: "unknown precip", BR: "mist", FG: "fog", HZ: "haze", FU: "smoke", DU: "dust", SA: "sand", VA: "volcanic ash",
    SH: "showers", FZ: "freezing", BL: "blowing", DR: "drifting", MI: "shallow", BC: "patches", PR: "partial", VC: "nearby", SQ: "squalls",
};
const WX_COVER = { FEW: "Few", SCT: "Scattered", BKN: "Broken", OVC: "Overcast", VV: "Obscured" };

function wxPlain(code) {
    // "-TSRA BR" -> "Light thunderstorm rain, mist"
    return String(code || "").trim().split(/\s+/).filter(Boolean).map(tok => {
        let pre = "";
        if (tok[0] === "-") { pre = "Light "; tok = tok.slice(1); }
        else if (tok[0] === "+") { pre = "Heavy "; tok = tok.slice(1); }
        const parts = (tok.match(/.{2}/g) || []).map(p => WX_CODES[p] || p);
        return pre + parts.join(" ");
    }).join(", ").replace(/^./, c => c.toUpperCase());
}

function cToF(c) { return Math.round(c * 9 / 5 + 32); }

function renderWx(d) {
    const el = $("wx");
    if (d && !d.station && !d.error) { el.hidden = true; return; }
    const m = d && d.metar;
    if (!m) {
        el.hidden = false;
        el.innerHTML = `<div><div class="t"><span class="stn">${esc((d && d.station) || "WX")}</span></div><div class="l">${esc(d && d.error ? "weather unavailable" : "loading weather")}</div></div>`;
        return;
    }
    const ageMin = m.obs ? Math.max(0, Math.round((Date.now() / 1000 - m.obs) / 60)) : null;
    const stale = ageMin !== null && ageMin > 90;
    const cat = m.cat && WX_CAT[m.cat] ? `<span class="cat" style="--cat:${WX_CAT[m.cat]}">${esc(m.cat)}</span>` : "";

    let wind;
    if (num(m.wspd) === 0) wind = "Calm";
    else if (num(m.wspd) !== null) {
        const dir = num(m.wdir);
        const arrow = dir !== null
            ? `<svg class="arrow" viewBox="0 0 24 24" style="transform:rotate(${(dir + 180) % 360}deg)"><path d="M12 2l6 10h-4v10h-4V12H6z"/></svg>`
            : "";
        wind = `${arrow}${dir !== null ? String(dir).padStart(3, "0") + "°" : "VRB"} ${m.wspd}${num(m.wgst) ? "G" + m.wgst : ""}<small>kt</small>`;
    } else wind = "—";

    const temp = num(m.temp) !== null ? `${cToF(m.temp)}°F<small>${Math.round(m.temp)}°C</small>` : "—";
    const dew = num(m.dewp) !== null ? `dew ${cToF(m.dewp)}°F` : "";
    const vis = m.visib !== null && m.visib !== undefined ? `${esc(m.visib)}<small>mi</small>` : "—";
    const baro = num(m.inhg) !== null ? `${Number(m.inhg).toFixed(2)}<small>inHg</small>` : "—";

    let sky = "Clear";
    const layers = (m.clouds || []).filter(c => WX_COVER[c.cover]);
    if (layers.length) {
        const ceil = layers.find(c => c.cover === "BKN" || c.cover === "OVC" || c.cover === "VV") || layers[0];
        sky = `${WX_COVER[ceil.cover]}${num(ceil.base) !== null ? " " + Number(ceil.base).toLocaleString() + "′" : ""}`;
    }
    const wxNow = m.wx ? wxPlain(m.wx) : "";

    el.hidden = false;
    el.classList.toggle("stale", stale);
    el.title = `${m.raw}${m.name ? "\n" + m.name : ""}${stale ? "\n(report is over 90 minutes old)" : ""}`;
    el.innerHTML = `
        <div><div class="t"><span class="stn">${esc(m.station || "")}</span>${cat}</div><div class="l">${ageMin !== null ? (ageMin < 1 ? "just now" : ageMin + " min ago") : "metar"}</div></div>
        <div><div class="t">${temp}</div><div class="l">${esc(dew) || "temp"}</div></div>
        <div><div class="t">${wind}</div><div class="l">wind</div></div>
        <div class="w-baro"><div class="t">${baro}</div><div class="l">altimeter</div></div>
        <div class="w-vis"><div class="t">${vis}</div><div class="l">visibility</div></div>
        <div class="w-sky"><div class="t">${esc(wxNow || sky)}</div><div class="l">${wxNow ? esc(sky) : "sky"}</div></div>`;
}

async function loadWx() {
    try {
        const res = await fetch("/api/metar", { cache: "no-store" });
        renderWx(await res.json());
    } catch (e) {
        renderWx({ error: "offline" });
    }
}

/* ---------- Flight timeline ---------- */
function fmtClock(ts, withSec = false) {
    return new Date(ts * 1000).toLocaleTimeString([], { hour: "2-digit", minute: "2-digit", ...(withSec ? { second: "2-digit" } : {}) });
}
function fmtZ(ts) {
    const d = new Date(ts * 1000);
    return String(d.getUTCHours()).padStart(2, "0") + ":" + String(d.getUTCMinutes()).padStart(2, "0") + "Z";
}
function fmtDur(sec) {
    if (!(sec > 0)) return "—";
    if (sec < 60) return "<1m";
    const h = Math.floor(sec / 3600), m = Math.round((sec % 3600) / 60);
    return h ? `${h}h ${String(m).padStart(2, "0")}m` : `${m}m`;
}

function profileChart(el, pts) {
    // pts: [[ts, alt]]; alt null = unknown, 0 = ground
    const data = pts.filter(p => num(p[1]) !== null);
    if (data.length < 2) { el.innerHTML = '<div class="tl-empty">Not enough ADS-B positions yet for an altitude profile.</div>'; return; }
    const W = Math.max(280, el.clientWidth || 500), H = 150, m = { l: 44, r: 8, t: 10, b: 22 };
    const t0 = data[0][0], t1 = data[data.length - 1][0];
    const peak = Math.max(...data.map(p => p[1]), 500) * 1.05;
    const step = [250, 500, 1000, 2000, 2500, 5000, 10000].find(st => peak / st <= 5) || 10000;
    const divs = Math.max(1, Math.ceil(peak / step));
    const maxA = divs * step;
    const x = t => m.l + (t - t0) / Math.max(1, t1 - t0) * (W - m.l - m.r);
    const y = a => m.t + (H - m.t - m.b) - a / maxA * (H - m.t - m.b);
    let path = "", area = "", seg = [];
    const segs = [];
    data.forEach((p, i) => {
        if (i && p[0] - data[i - 1][0] > 180) { segs.push(seg); seg = []; }   // gap in coverage: break the line
        seg.push(p);
    });
    segs.push(seg);
    for (const s of segs) {
        path += s.map((p, i) => (i ? "L" : "M") + x(p[0]).toFixed(1) + "," + y(p[1]).toFixed(1)).join("");
        if (s.length > 1) area += `M${x(s[0][0]).toFixed(1)},${y(0)}` + s.map(p => "L" + x(p[0]).toFixed(1) + "," + y(p[1]).toFixed(1)).join("") + `L${x(s[s.length - 1][0]).toFixed(1)},${y(0)}Z`;
    }
    let grid = "";
    for (let k = 0; k <= divs; k++) {
        const v = step * k, yy = y(v).toFixed(1);
        if (k) grid += `<line class="gl" x1="${m.l}" x2="${W - m.r}" y1="${yy}" y2="${yy}"/>`;
        grid += `<text class="yt" x="${m.l - 6}" y="${(+yy + 3.5).toFixed(1)}">${fmtK(v)}</text>`;
    }
    const nT = Math.min(5, Math.max(2, Math.floor((W - m.l) / 90)));
    let ticks = "";
    for (let k = 0; k < nT; k++) {
        const t = t0 + (t1 - t0) * k / (nT - 1);
        ticks += `<text class="xt" x="${x(t).toFixed(1)}" y="${H - 6}" style="text-anchor:${k === 0 ? "start" : k === nT - 1 ? "end" : "middle"}">${fmtClock(t, t1 - t0 < 600)}</text>`;
    }
    el.innerHTML = `<svg viewBox="0 0 ${W} ${H}" style="height:${H}px">${grid}
        <path d="${area}" fill="rgba(56,189,248,0.12)"/>
        <path d="${path}" fill="none" stroke="#38bdf8" stroke-width="2" stroke-linejoin="round"/>
        <line class="base" x1="${m.l}" x2="${W - m.r}" y1="${y(0)}" y2="${y(0)}"/>${ticks}
        <line class="cross" id="pf-x" y1="${m.t}" y2="${y(0)}" visibility="hidden"/>
        <circle id="pf-dot" r="4" fill="#38bdf8" stroke="#0c121c" stroke-width="2" visibility="hidden"/>
        <rect x="${m.l}" y="${m.t}" width="${W - m.l - m.r}" height="${H - m.t - m.b}" fill="transparent" style="cursor:crosshair"/></svg>
        <div class="ctip" hidden></div>`;
    const svg = el.querySelector("svg"), tip = el.querySelector(".ctip");
    const cx = el.querySelector("#pf-x"), dot = el.querySelector("#pf-dot");
    svg.onmousemove = e => {
        const r = svg.getBoundingClientRect();
        const px = (e.clientX - r.left) * W / r.width;
        const t = t0 + (px - m.l) / (W - m.l - m.r) * (t1 - t0);
        let best = data[0];
        for (const p of data) if (Math.abs(p[0] - t) < Math.abs(best[0] - t)) best = p;
        const bx = x(best[0]), by = y(best[1]);
        cx.setAttribute("x1", bx); cx.setAttribute("x2", bx); cx.setAttribute("visibility", "visible");
        dot.setAttribute("cx", bx); dot.setAttribute("cy", by); dot.setAttribute("visibility", "visible");
        tip.innerHTML = tipRows(fmtClock(best[0], true), [["Altitude", best[1] === 0 ? "Ground" : Math.round(best[1]).toLocaleString() + " ft", "#38bdf8"]]);
        tip.hidden = false;
        let left = bx * r.width / W + 12;
        if (left + tip.offsetWidth > r.width) left = bx * r.width / W - tip.offsetWidth - 12;
        tip.style.left = Math.max(0, left) + "px";
        tip.style.top = "0px";
    };
    svg.onmouseleave = () => { tip.hidden = true; cx.setAttribute("visibility", "hidden"); dot.setAttribute("visibility", "hidden"); };
}

function renderDrawer() {
    const d = S.dr && S.dr.data;
    const el = $("drawer");
    if (!d) { el.innerHTML = '<div class="tl-empty">Loading&hellip;</div>'; return; }
    const ac = d.aircraft || {};
    const flight = String(d.flight || ac.flight || "").trim().toUpperCase();
    const tail = String(d.tail || "").toUpperCase();
    const airline = airlineFromFlight(flight);
    const heli = isHeli(ac);
    const ident = flight || tail || String(d.hex || "").toUpperCase() || "Unknown";
    const sub = [airline, tail && tail !== ident ? tail : "", ac.t, heli ? "Helicopter" : "", d.hex ? "hex " + d.hex.toUpperCase() : ""].filter(Boolean).join(" · ");
    const r = d.route;

    const cell = (k) => {
        const c = o[k];
        return `<div><div class="k">${k}</div>${c
            ? `<div class="v">${fmtClock(c.ts)}</div><div class="z">${fmtZ(c.ts)}${c.detected ? " · detected " + esc(c.detected) : c.reported ? "" : " · msg time"}</div>`
            : '<div class="v na">—</div><div class="z">&nbsp;</div>'}</div>`;
    };
    const o = Object.assign({}, d.oooi);
    for (const ev of d.airport_events || []) {
        if (ev.type === "departure" && !o.OFF) o.OFF = { ts: ev.ts, detected: ev.code };
        if (ev.type === "arrival" && !o.ON && (!o.OFF || ev.ts > o.OFF.ts)) o.ON = { ts: ev.ts, detected: ev.code };
    }
    const block = o.OUT && o.IN ? o.IN.ts - o.OUT.ts : (o.OUT && !o.IN ? Date.now() / 1000 - o.OUT.ts : null);
    const air = o.OFF && o.ON ? o.ON.ts - o.OFF.ts : (o.OFF && !o.ON ? Date.now() / 1000 - o.OFF.ts : null);
    const hasOooi = Object.keys(o).length > 0;

    // Timeline items: messages + airport events + OOOI moments
    const items = [];
    for (const m of d.messages) items.push({ ts: m.ts, kind: "msg", m });
    for (const ev of d.airport_events || []) items.push({ ts: ev.ts, kind: "ap", ev });
    items.sort((a, b) => a.ts - b.ts);
    const hideNoise = S.hideNoise;
    let hidden = 0;
    const rows = items.map(it => {
        if (it.kind === "ap") {
            const dep = it.ev.type === "departure";
            return `<div class="tl-item ev ${dep ? "dep" : "arr"}"><div class="tl-top"><span class="t">${fmtClock(it.ts, true)}</span><span>${dep ? "&#8599; Departed" : "&#8600; Arriving"} ${esc(it.ev.name || it.ev.code)}</span></div>
                <div class="tl-dec">Detected from ADS-B${it.ev.vr !== null && it.ev.vr !== undefined ? ` · ${it.ev.vr > 0 ? "+" : ""}${it.ev.vr} fpm` : ""}${it.ev.agl !== null && it.ev.agl !== undefined ? ` · ${it.ev.agl.toLocaleString()} ft above field` : ""}</div></div>`;
        }
        const m = it.m;
        if (hideNoise && m.noise && !m.alert && !m.oooi) { hidden++; return ""; }
        const src = String(m.source || "").toLowerCase();
        const meta = [m.msg_type || (m.label ? "Label " + m.label : ""), num(m.freq) !== null ? Number(m.freq).toFixed(3) : "",
            num(m.distance) !== null ? `✓ ${Number(m.distance).toFixed(1)} mi ${m.cardinal || ""}` : ""].filter(Boolean).join(" · ");
        return `<div class="tl-item s-${esc(src)} ${m.oooi ? "oooi-ev" : ""}">
            <div class="tl-top"><span class="t">${fmtClock(m.ts, true)}</span><span class="src">${esc(src.toUpperCase())}</span><span>${esc(meta)}</span></div>
            ${m.decoded ? `<div class="tl-dec">${highlight(m.decoded)}</div>` : ""}
            ${m.text ? `<pre class="tl-raw" title="Click to expand">${highlight(m.text)}</pre>` : ""}
        </div>`;
    }).join("");

    el.innerHTML = `
        <div class="dr-head">
            ${acAvatar(ac, airline, ident)}
            <div class="dr-id"><div class="big">${esc(ident)}${S.events[d.hex] ? apBadge(S.events[d.hex]) : ""}</div><div class="s">${esc(sub) || "&nbsp;"}</div></div>
            <button class="dr-close" id="dr-close" title="Close (Esc)">&times;</button>
        </div>
        <div class="dr-actions">
            ${d.live && d.hex ? `<button data-focus="${esc(d.hex)}">Show on map</button>` : ""}
            ${d.hex ? `<a class="btn" href="https://globe.adsbexchange.com/?icao=${encodeURIComponent(d.hex)}" target="_blank" rel="noopener">ADS-B Exchange &#8599;</a>` : ""}
        </div>
        ${!r && d.route_rejected ? `<div class="dr-sec"><h4>Route</h4><div class="tl-empty">Unknown &mdash; the route database lists ${esc(d.route_rejected)} for this flight number, but the aircraft's position doesn't fit it (flight numbers are often reused for different legs).</div></div>` : ""}
        ${r ? `<div class="dr-sec"><h4>Route</h4><div class="dr-route">${esc(rtShort(r))}<small>${esc(rtLong(r))}</small></div>
            <div class="pop-rsrc ${r.src === "radio" ? "radio" : ""}" style="max-width:none;margin-top:4px">${esc(rtSourceNote(r))}</div></div>` : ""}
        ${hasOooi || d.messages.length ? `<div class="dr-sec"><h4>Out &middot; Off &middot; On &middot; In <span>local time</span></h4>
            <div class="oooi">${["OUT", "OFF", "ON", "IN"].map(cell).join("")}</div>
            ${hasOooi ? `<div class="durs">${o.OUT ? `<span>Block time <b>${fmtDur(block)}</b>${!o.IN ? " so far" : ""}</span>` : ""}${o.OFF ? `<span>Air time <b>${fmtDur(air)}</b>${!o.ON ? " so far" : ""}</span>` : ""}</div>`
                : '<div class="durs">No OUT/OFF/ON/IN reports received for this flight yet.</div>'}
        </div>` : ""}
        <div class="dr-sec"><h4>Altitude <span>${d.live ? "live ADS-B" : "while in range"}</span></h4><div class="prof" id="dr-prof"></div></div>
        <div class="dr-sec"><h4>Timeline <span>${d.messages.length} message${d.messages.length === 1 ? "" : "s"}${hidden ? ` · ${hidden} noise hidden` : ""}</span></h4>
            ${rows ? `<div class="tl-list">${rows}</div>` : '<div class="tl-empty">No radio messages from this flight in the last 24 hours.</div>'}
        </div>`;
    profileChart($("dr-prof"), d.profile || []);
}

async function loadDrawer() {
    const q = S.dr && S.dr.q;
    if (!q) return;
    try {
        const res = await fetch("/api/flight?" + new URLSearchParams(q).toString(), { cache: "no-store" });
        const data = await res.json();
        if (!S.dr || S.dr.q !== q) return;
        const scroll = $("drawer").scrollTop;
        const open = [...$("drawer").querySelectorAll(".tl-raw")].map(p => p.classList.contains("open"));
        S.dr.data = data;
        renderDrawer();
        $("drawer").querySelectorAll(".tl-raw").forEach((p, i) => { if (open[i]) p.classList.add("open"); });
        $("drawer").scrollTop = scroll;
    } catch (e) {}
}

function openFlight(q) {
    const clean = {};
    for (const [k, v] of Object.entries(q)) if (v) clean[k] = v;
    if (!Object.keys(clean).length) return;
    S.dr = { q: clean, data: null, timer: null };
    $("drawer").hidden = false;
    $("dr-bg").hidden = false;
    renderDrawer();
    loadDrawer();
    S.dr.timer = setInterval(loadDrawer, 10000);
}

function closeFlight() {
    if (S.dr) clearInterval(S.dr.timer);
    S.dr = null;
    $("drawer").hidden = true;
    $("dr-bg").hidden = true;
}

/* ---------- Radio-reported positions ---------- */
let posLayer = null;
const posMarkers = new Map();

function normReg(r) {
    return String(r || "").replace(/[^A-Za-z0-9]/g, "").toUpperCase().replace(/^N/, "");
}

async function fetchPositions() {
    try {
        const res = await fetch("/acars_positions.json", { cache: "no-store" });
        if (!res.ok) return;
        const json = await res.json();
        S.positions = json.positions || [];
        S.posByKey = new Map(S.positions.map(p => [p.key, p]));
    } catch (e) {}
}

function adsbCovers(p) {
    for (const h of [p.adsb_hex, p.hex]) {
        if (h && S.acByHex.has(String(h).toLowerCase())) return true;
    }
    const reg = normReg(p.tail);
    if (reg.length >= 3 && S.adsbRegs.has(reg)) return true;
    const fl = String(p.flight || "").replace(/[^A-Za-z0-9]/g, "").toUpperCase();
    return fl.length >= 3 && S.adsbFlights.has(fl);
}

function posIdent(p) {
    return String(p.flight || "").trim().toUpperCase() || String(p.tail || "").toUpperCase() || String(p.hex || "").toUpperCase() || "?";
}

function posHtml(p) {
    const age = Date.now() / 1000 - (p.ts || 0);
    const op = Math.max(0.4, Math.min(1, 1 - age / 1800 * 0.6)).toFixed(1);
    const label = S.labels ? `<span class="pl-lbl">${esc(posIdent(p))}</span>` : "";
    return `<div class="ap s-${esc(p.source)}" style="opacity:${op}"><i></i>${label}</div>`;
}

function posPopup(key) {
    const p = S.posByKey.get(key);
    if (!p) return "<i>Position report expired</i>";
    const airline = airlineFromFlight(p.flight);
    const rows = [
        ["Source", String(p.source || "radio").toUpperCase()],
        ["Reported", timeAgo(p.ts)],
        num(p.alt) !== null ? ["Altitude", Number(p.alt).toLocaleString() + " ft"] : null,
        ["From home", `${Number(p.distance).toFixed(1)} mi ${p.cardinal || ""}`],
        p.tail ? ["Reg", p.tail] : null,
    ].filter(Boolean);
    return `<div class="pop-id">${esc(posIdent(p))}</div>
        <div class="pop-sub">${esc([airline, p.hex ? "hex " + String(p.hex).toUpperCase() : ""].filter(Boolean).join(" · ")) || "&nbsp;"}</div>
        ${routePopupBlock(p.route)}
        ${rows.map(([k, v]) => `<div class="pop-row"><span>${esc(k)}</span><span>${esc(v)}</span></div>`).join("")}
        ${p.summary ? `<div class="pop-sum">${esc(p.summary)}</div>` : ""}
        <div class="pop-note">&#9670; Position from the aircraft's own radio report &mdash; not currently seen on ADS-B</div>`;
}

function updatePositions() {
    if (!map || !posLayer) return 0;
    const live = new Set();
    if (S.showPos) {
        for (const p of S.positions) {
            if (num(p.lat) === null || num(p.lon) === null || adsbCovers(p)) continue;
            live.add(p.key);
            const html = posHtml(p);
            let m = posMarkers.get(p.key);
            if (!m) {
                m = L.marker([p.lat, p.lon], { icon: L.divIcon({ className: "", html, iconSize: [16, 16], iconAnchor: [8, 8] }) });
                m._html = html;
                m._key = p.key;
                const key = p.key;
                m.bindPopup(() => posPopup(key));
                posLayer.addLayer(m);
                posMarkers.set(p.key, m);
            } else {
                m.setLatLng([p.lat, p.lon]);
                if (m._html !== html) {
                    m._html = html;
                    m.setIcon(L.divIcon({ className: "", html, iconSize: [16, 16], iconAnchor: [8, 8] }));
                }
                if (m.isPopupOpen()) m.setPopupContent(posPopup(p.key));
            }
        }
    }
    for (const [k, m] of posMarkers) {
        if (!live.has(k)) {
            posLayer.removeLayer(m);
            posMarkers.delete(k);
        }
    }
    return live.size;
}

function focusPos(key) {
    const p = S.posByKey.get(key);
    // If ADS-B already has this aircraft, show the live plane instead.
    if (p) {
        for (const h of [p.adsb_hex, p.hex]) {
            if (h && S.acByHex.has(String(h).toLowerCase())) { focusPlane(h); return; }
        }
    }
    setTab("map");
    setTimeout(() => {
        if (!map) return;
        mapFitted = true;
        const m = posMarkers.get(key);
        if (m) {
            map.flyTo(m.getLatLng(), Math.max(map.getZoom(), 8), { duration: 0.8 });
            setTimeout(() => m.openPopup(), 850);
        } else if (p) {
            map.flyTo([p.lat, p.lon], Math.max(map.getZoom(), 8), { duration: 0.8 });
        } else {
            toast({ kind: "info", title: "POSITION EXPIRED", main: "Not on map", detail: "That report is older than 30 minutes." });
        }
    }, 120);
}

/* ---------- Trends ---------- */
const C_ACARS = "#fbbf24", C_VDLM2 = "#a78bfa", C_VER = "#22e584", C_REST = "#64748b", C_HOD = "#7c93b5";

function niceMax(v) {
    if (v <= 0) return 1;
    const p = 10 ** Math.floor(Math.log10(v));
    for (const f of [1, 2, 2.5, 5, 10]) if (f * p >= v) return f * p;
    return 10 * p;
}

function fmtK(v) {
    if (v >= 10000) return Math.round(v / 1000) + "k";
    if (v >= 1000) return (v / 1000).toFixed(1).replace(/\.0$/, "") + "k";
    return String(Math.round(v * 10) / 10);
}

function legend(items) {
    return items.map(([name, color]) => `<span class="lgi"><i style="background:${color}"></i>${esc(name)}</span>`).join("");
}

function barChart(el, { labels, series, tip, tickEvery = 1, colorAt = null, height = 190 }) {
    const W = Math.max(260, el.clientWidth || 600), H = height;
    const m = { l: 38, r: 6, t: 10, b: 22 };
    const n = labels.length;
    const totals = labels.map((_, i) => series.reduce((s, se) => s + (se.values[i] || 0), 0));
    const max = niceMax(Math.max(...totals, 1));
    const iw = W - m.l - m.r, ih = H - m.t - m.b;
    const band = iw / Math.max(1, n);
    const bw = Math.max(2, Math.min(24, band * 0.72));
    const y = v => m.t + ih - (v / max) * ih;

    let grid = "", bars = "", hits = "", ticks = "";
    for (let k = 0; k <= 4; k++) {
        const v = max * k / 4, yy = y(v).toFixed(1);
        if (k) grid += `<line class="gl" x1="${m.l}" x2="${W - m.r}" y1="${yy}" y2="${yy}"/>`;
        grid += `<text class="yt" x="${m.l - 6}" y="${(+yy + 3.5).toFixed(1)}">${fmtK(v)}</text>`;
    }
    labels.forEach((lab, i) => {
        const x = (m.l + band * i + (band - bw) / 2).toFixed(1);
        let acc = 0;
        series.forEach(se => {
            const v = se.values[i] || 0;
            if (!v) return;
            const y0 = y(acc), y1 = y(acc + v);
            const h = Math.max(1, y0 - y1 - (acc > 0 ? 2 : 0));
            const fill = colorAt ? colorAt(i, se) : se.color;
            bars += `<rect x="${x}" y="${y1.toFixed(1)}" width="${bw.toFixed(1)}" height="${h.toFixed(1)}" rx="2" fill="${fill}"/>`;
            acc += v;
        });
        hits += `<rect class="hit" data-i="${i}" x="${(m.l + band * i).toFixed(1)}" y="${m.t}" width="${band.toFixed(1)}" height="${ih}"/>`;
        if (i % tickEvery === 0 && lab) ticks += `<text class="xt" x="${(m.l + band * i + band / 2).toFixed(1)}" y="${H - 6}">${esc(lab)}</text>`;
    });
    const base = `<line class="base" x1="${m.l}" x2="${W - m.r}" y1="${m.t + ih}" y2="${m.t + ih}"/>`;

    el.innerHTML = `<svg viewBox="0 0 ${W} ${H}" style="height:${H}px" role="img">${grid}${bars}${base}${ticks}${hits}</svg><div class="ctip" hidden></div>`;
    const tipEl = el.querySelector(".ctip");
    el.onmousemove = e => {
        const hit = e.target.closest(".hit");
        if (!hit) { tipEl.hidden = true; return; }
        tipEl.innerHTML = tip(+hit.dataset.i);
        tipEl.hidden = false;
        const r = el.getBoundingClientRect();
        let left = e.clientX - r.left + 14;
        if (left + tipEl.offsetWidth > r.width) left = e.clientX - r.left - tipEl.offsetWidth - 14;
        tipEl.style.left = Math.max(0, left) + "px";
        tipEl.style.top = Math.max(0, e.clientY - r.top - tipEl.offsetHeight - 10) + "px";
    };
    el.onmouseleave = () => { tipEl.hidden = true; };
}

function tipRows(title, rows) {
    return `<div class="tt">${esc(title)}</div>` + rows.map(([name, val, color]) =>
        `<div class="row"><span>${color ? `<i style="background:${color}"></i>` : ""}${esc(name)}</span><span>${esc(val)}</span></div>`).join("");
}

function hbarList(el, entries, color, empty) {
    if (!entries.length) { el.innerHTML = `<div class="na" style="font-size:12px">${esc(empty)}</div>`; return; }
    const max = Math.max(...entries.map(e => e[1]), 1);
    el.innerHTML = entries.map(([name, c]) => `<div class="hb-row" style="--c:${color}" title="${esc(name)}: ${c.toLocaleString()}">
        <span class="nm">${esc(name)}</span>
        <span class="track"><div style="width:${(c / max * 100).toFixed(1)}%"></div></span>
        <span class="n">${c.toLocaleString()}</span>
    </div>`).join("");
}

function hourLabel(h) { return String(h).padStart(2, "0") + ":00"; }

function renderTrends() {
    const d = T.data;
    if (!d) return;
    if (!d.ok) { $("t-note").textContent = "Trends unavailable: " + (d.error || "unknown error"); return; }

    const today = d.daily[d.daily.length - 1] || { total: 0 };
    const avg = d.total / Math.max(1, d.ndays);
    const pct = d.total ? d.verified / d.total * 100 : 0;
    const peak = d.hod.reduce((b, v, i) => (v > d.hod[b] ? i : b), 0);
    const far = d.farthest;
    const tile = (k, v, h, c) => `<div class="kpi" style="--c:${c}"><div class="k">${k}</div><div class="v">${v}</div><div class="h">${h}</div></div>`;
    $("t-kpis").innerHTML = [
        tile("Today", today.total.toLocaleString(), "messages so far", "var(--text)"),
        tile("Daily average", Math.round(avg).toLocaleString(), `over ${d.ndays} day${d.ndays === 1 ? "" : "s"} with data`, "var(--acars)"),
        tile("Verified", pct.toFixed(1) + "<small>%</small>", `${d.verified.toLocaleString()} matched to ADS-B`, "var(--ok)"),
        tile("Busiest hour", d.total ? hourLabel(peak) : "—", d.total ? `avg ${Math.round(d.hod[peak])} messages` : "no data yet", "var(--vdlm2)"),
        tile("Farthest verified", far ? Math.round(far.distance) + "<small> mi</small>" : "—", far ? esc([far.flight || far.tail, new Date(far.ts * 1000).toLocaleDateString([], { month: "short", day: "numeric" })].filter(Boolean).join(" · ")) : "none yet", "var(--adsb)"),
        tile("Position reports", d.positions.toLocaleString(), "aircraft-reported positions", "#34d399"),
    ].join("");

    // Hourly, last 48h
    const hourly = d.hourly;
    const hourStep = ($("c-hourly").clientWidth || 600) < 520 ? 12 : 6;
    $("lg-hourly").innerHTML = legend([["ACARS", C_ACARS], ["VDLM2", C_VDLM2]]);
    barChart($("c-hourly"), {
        labels: hourly.map(h => { const t = new Date(h.t * 1000); return t.getHours() % hourStep === 0 ? hourLabel(t.getHours()) : ""; }),
        series: [{ name: "ACARS", color: C_ACARS, values: hourly.map(h => h.acars) }, { name: "VDLM2", color: C_VDLM2, values: hourly.map(h => h.vdlm2) }],
        tip: i => {
            const h = hourly[i], t = new Date(h.t * 1000);
            return tipRows(`${t.toLocaleDateString([], { weekday: "short" })} ${hourLabel(t.getHours())}–${hourLabel((t.getHours() + 1) % 24)}`,
                [["ACARS", h.acars.toLocaleString(), C_ACARS], ["VDLM2", h.vdlm2.toLocaleString(), C_VDLM2], ["Total", (h.acars + h.vdlm2).toLocaleString()]]);
        },
    });

    // Daily
    const daily = d.daily;
    const dayFmt = s => new Date(s + "T12:00:00").toLocaleDateString([], { month: "short", day: "numeric" });
    $("lg-daily").innerHTML = legend([["Verified", C_VER], ["Not verified", C_REST]]);
    barChart($("c-daily"), {
        labels: daily.map(x => dayFmt(x.date)),
        tickEvery: Math.ceil(daily.length / 10),
        series: [
            { name: "Verified", color: C_VER, values: daily.map(x => x.verified) },
            { name: "Not verified", color: C_REST, values: daily.map(x => x.total - x.verified) },
        ],
        tip: i => {
            const x = daily[i];
            const p = x.total ? (x.verified / x.total * 100).toFixed(1) + "%" : "—";
            return tipRows(new Date(x.date + "T12:00:00").toLocaleDateString([], { weekday: "short", month: "short", day: "numeric" }), [
                ["Messages", x.total.toLocaleString()],
                ["Verified", `${x.verified.toLocaleString()} (${p})`, C_VER],
                ["Position reports", x.positions.toLocaleString()],
                ["Farthest verified", x.max_dist ? Math.round(x.max_dist) + " mi" : "—"],
            ]);
        },
    });

    // Hour of day
    const nowH = new Date().getHours();
    barChart($("c-hod"), {
        labels: d.hod.map((_, i) => (i % 6 === 0 ? hourLabel(i) : "")),
        series: [{ name: "Average", color: C_HOD, values: d.hod }],
        colorAt: i => (i === nowH ? "#e8eef6" : C_HOD),
        height: 170,
        tip: i => tipRows(`${hourLabel(i)}–${hourLabel((i + 1) % 24)}${i === nowH ? " (now)" : ""}`, [["Avg messages", d.hod[i].toLocaleString()]]),
    });

    hbarList($("c-types"), d.types, "#7c93b5", "No messages logged yet.");
    hbarList($("c-airlines"), d.airlines, "#38bdf8", "No airline traffic logged yet.");

    const since = d.oldest ? new Date(d.oldest * 1000).toLocaleDateString([], { month: "short", day: "numeric" }) : null;
    $("t-note").textContent = `Updated ${new Date(d.generated * 1000).toLocaleTimeString([], { hour: "2-digit", minute: "2-digit" })}` +
        (since ? ` · logging since ${since}` : " · logging just started — the first rows land within a minute");
}

async function loadTrends(force = false) {
    if (T.loading) return;
    if (!force && T.data && Date.now() - T.last < 60000) { renderTrends(); return; }
    T.loading = true;
    try {
        const res = await fetch(`/api/trends?days=${T.days}`, { cache: "no-store" });
        T.data = await res.json();
        T.last = Date.now();
    } catch (e) {
        T.data = { ok: false, error: "could not reach the dashboard server" };
    } finally {
        T.loading = false;
    }
    if (S.tab === "trends") renderTrends();
}

/* ---------- Tabs ---------- */
function setTab(tab) {
    S.tab = tab;
    document.querySelectorAll(".tab").forEach(b => b.classList.toggle("on", b.dataset.tab === tab));
    ["live", "map", "nearby", "alerts", "trends"].forEach(t => { $("v-" + t).hidden = t !== tab; });
    $("kpis").hidden = tab !== "live";      // count tiles only on the Live tab
    if (tab === "trends") loadTrends();
    try { localStorage.setItem("avdash-tab", tab); } catch (e) {}

    if (tab === "map" && map) {
        setTimeout(() => {
            sizeMap();
            map.invalidateSize();
            if (!mapFitted && markers.size) {
                fitMap();
                mapFitted = true;
            }
        }, 60);
    }
    if (tab === "alerts") {
        S.unseenAlerts = 0;
        updateAlertBadge();
    }
    if (tab === "nearby") document.querySelector('.tab[data-tab="nearby"]').classList.remove("hot");
}

// Let the map fill the window below the tabs (phones keep their own fixed height).
function sizeMap() {
    const el = $("map");
    if (!el) return;
    if (window.innerWidth <= 640) { el.style.height = ""; return; }
    const top = el.getBoundingClientRect().top + window.scrollY;
    el.style.height = Math.max(460, Math.round(window.innerHeight - top - 24)) + "px";
}
window.addEventListener("resize", () => {
    if (S.tab === "map" && map) { sizeMap(); map.invalidateSize(); }
});

/* ---------- WebSocket ---------- */
let ws = null;
let wsRetry = 0;

function connect() {
    const proto = location.protocol === "https:" ? "wss" : "ws";
    ws = new WebSocket(`${proto}://${location.hostname}:${WS_PORT}`);

    ws.onopen = () => {
        wsRetry = 0;
        light("link", true);
    };

    ws.onclose = () => {
        light("link", false);
        light("acars", false);
        light("vdlm2", false);
        $("foot-left").textContent = "Connection lost — reconnecting…";
        setTimeout(connect, Math.min(15000, 1000 * 2 ** wsRetry++));
    };

    ws.onerror = () => {
        try { ws.close(); } catch (e) {}
    };

    ws.onmessage = ev => {
        let p;
        try { p = JSON.parse(ev.data); } catch (e) { return; }

        if (p.type === "status") {
            onStatus(p);
        } else if (p.type === "message") {
            addMessage(p.data);
        } else if (p.type === "history") {
            S.messages = (p.messages || []).slice().reverse().slice(0, MAX_FEED);
            renderFeed();
        } else if (p.type === "alert_terms_saved") {
            onTermsSaved(p);
        } else if (p.type === "alert_history") {
            S.alerts = (p.messages || []).slice().reverse();
            if (p.reset) S.unseenAlerts = 0;
            renderAlerts();
            updateAlertBadge();
        } else if (p.type === "notify") {
            const dist = num(p.distance);
            toast({
                kind: "verified",
                title: `VERIFIED ${String(p.source || "RADIO").toUpperCase()}`,
                main: String(p.flight || "").toUpperCase() || "Unknown",
                detail: `${p.airline ? p.airline + " · " : ""}${dist !== null ? "~" + Math.round(dist) + " mi" : ""} ${p.cardinal ? "to the " + p.cardinal : ""}`,
                hex: p.hex,
                airline: p.airline,
            });
        }
    };
}

setInterval(() => {
    if (ws && ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify({ type: "ping" }));
}, 30000);

/* ---------- Events ---------- */
document.addEventListener("click", e => {
    const rb = e.target.closest("#t-range button");
    if (rb) {
        T.days = Number(rb.dataset.days);
        document.querySelectorAll("#t-range button").forEach(b => b.classList.toggle("on", b === rb));
        loadTrends(true);
        return;
    }

    const st = e.target.closest("[data-star]");
    if (st) { toggleStar(st.dataset.star); return; }
    if (e.target.closest("#alerts-reset")) { resetAlertsClick(); return; }
    if (e.target.closest("#edit-terms")) { TE.open ? closeTermsEditor() : openTermsEditor(); return; }
    const tdel = e.target.closest("[data-te-del]");
    if (tdel) { TE.list.splice(Number(tdel.dataset.teDel), 1); TE.dirty = true; renderTermsEditor(); return; }
    if (e.target.closest("#te-add-btn")) { addTerm(); return; }
    if (e.target.closest("#te-save")) { saveTerms(); return; }
    if (e.target.closest("#te-cancel")) { closeTermsEditor(); return; }

    const tl = e.target.closest("[data-tl]");
    if (tl) {
        e.preventDefault();
        openFlight({ flight: tl.dataset.tlFlight, tail: tl.dataset.tlTail, hex: tl.dataset.tlHex });
        return;
    }
    if (e.target.closest("#dr-close") || e.target.id === "dr-bg") { closeFlight(); return; }
    const raw = e.target.closest(".tl-raw");
    if (raw && !window.getSelection().toString()) { raw.classList.toggle("open"); return; }
    const drFocus = e.target.closest(".drawer [data-focus]");
    if (drFocus) { closeFlight(); focusPlane(drFocus.dataset.focus); return; }

    const pos = e.target.closest("[data-pos]");
    if (pos) { focusPos(pos.dataset.pos); return; }

    const tab = e.target.closest(".tab");
    if (tab) { setTab(tab.dataset.tab); return; }

    const f = e.target.closest(".fchip");
    if (f) {
        S.filter = f.dataset.filter;
        document.querySelectorAll(".fchip").forEach(b => b.classList.toggle("on", b === f));
        renderFeed();
        return;
    }

    const focus = e.target.closest("[data-focus]");
    if (focus && focus.dataset.focus) { focusPlane(focus.dataset.focus); return; }

    const pre = e.target.closest(".m-text");
    if (pre && !window.getSelection().toString()) {
        pre.closest(".msg").classList.toggle("open");
    }
});

$("q").addEventListener("input", e => {
    S.q = e.target.value;
    renderFeed();
});

$("pause").addEventListener("click", () => {
    S.paused = !S.paused;
    if (!S.paused) renderFeed();
    else renderPending();
});

$("pending").addEventListener("click", () => {
    S.paused = false;
    renderFeed();
});

$("m-labels").addEventListener("click", e => {
    S.labels = !S.labels;
    e.currentTarget.classList.toggle("on", S.labels);
    updateMap();
});
$("m-fit").addEventListener("click", fitMap);
$("m-home").addEventListener("click", () => map && map.setView([HOME_LAT, HOME_LON], 9));
$("lg-heli").innerHTML = heliIcon(false);
document.addEventListener("input", e => { if (e.target.id === "te-input") termHint(); });
document.addEventListener("keydown", e => {
    if (e.target.id === "te-input" && e.key === "Enter") { e.preventDefault(); addTerm(); }
});
loadWx();
setInterval(loadWx, 60000);
document.addEventListener("keydown", e => { if (e.key === "Escape" && S.dr) closeFlight(); });
$("m-radar").addEventListener("click", () => setRadar(!RADAR.on));
$("m-loop").addEventListener("click", () => radarLoop(!RADAR.loop));
try { if (localStorage.getItem("avdash-radar") === "1") setTimeout(() => setRadar(true), 800); } catch (e) {}
$("m-trails").addEventListener("click", () => setTrails(!S.showTrails));
$("m-cov").addEventListener("click", () => setCoverage(!S.showCov));
try { if (localStorage.getItem("avdash-cov") === "1") setTimeout(() => setCoverage(true), 700); } catch (e) {}
try { if (localStorage.getItem("avdash-trails") === "1") setTimeout(() => setTrails(true), 500); } catch (e) {}
$("m-pos").addEventListener("click", e => {
    S.showPos = !S.showPos;
    e.currentTarget.classList.toggle("on", S.showPos);
    updateMap();
});
$("noise").addEventListener("click", e => {
    S.hideNoise = !S.hideNoise;
    e.currentTarget.classList.toggle("on", S.hideNoise);
    try { localStorage.setItem("avdash-hidenoise", S.hideNoise ? "1" : "0"); } catch (err) {}
    renderFeed();
});
try {
    S.hideNoise = localStorage.getItem("avdash-hidenoise") === "1";
    $("noise").classList.toggle("on", S.hideNoise);
} catch (e) {}

let resizeTimer = null;
window.addEventListener("resize", () => {
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(() => {
        if (S.tab === "trends") renderTrends();
        if (S.dr && S.dr.data) profileChart($("dr-prof"), S.dr.data.profile || []);
    }, 150);
});
setInterval(() => { if (S.tab === "trends") loadTrends(true); }, 300000);

/* ---------- Start ---------- */
initMap();
renderDist([0, 0, 0, 0, 0]);
renderFreqs({});
renderAirlines({});
renderFeed();
renderAlerts();
setTerms([]);
try {
    const saved = localStorage.getItem("avdash-tab");
    if (saved && $("v-" + saved)) setTab(saved);
} catch (e) {}
tick();
setInterval(tick, 1000);
connect();
fetchAdsb();
setInterval(fetchAdsb, 3000);
</script>
</body>
</html>
"""

# =========================
# Main
# =========================
async def main():
    if not HOME_LAT and not HOME_LON:
        print("[SETTINGS] HOME_LAT / HOME_LON are not set: distances, the map and Nearby won't be right. "
              "Set them in my_settings.py.")
    load_state()
    load_alerts_history()
    load_stored_history()
    for _m in stored_messages:
        try:
            log_flight_message(_m)
        except Exception:
            pass
    load_alert_terms()
    load_watchlist()
    db_init()
    load_route_cache()
    load_coverage()
    threading.Thread(target=_load_airports_csv, daemon=True).start()
    threading.Thread(target=route_lookup_loop, daemon=True).start()
    threading.Thread(target=metar_loop, daemon=True).start()
    threading.Thread(target=pushover_loop, daemon=True).start()
    print("[PUSHOVER] " + ("enabled for alert messages" if all(_pushover_keys()) else "off (no keys set)"))

    signal.signal(signal.SIGTERM, _on_shutdown)
    signal.signal(signal.SIGINT,  _on_shutdown)

    global MAIN_LOOP
    MAIN_LOOP = asyncio.get_running_loop()

    # HTTP (threaded so a slow request never blocks the page)
    server = ThreadingHTTPServer(("0.0.0.0", HTTP_PORT), Handler)
    server.daemon_threads = True
    threading.Thread(target=server.serve_forever, daemon=True).start()

    # ADS-B poller
    threading.Thread(target=adsb_poll_loop, daemon=True).start()

    # WebSocket
    import websockets
    await websockets.serve(ws_handler, "0.0.0.0", WS_PORT)

    # Periodics
    asyncio.create_task(periodic_state_save())
    asyncio.create_task(periodic_history_save())
    asyncio.create_task(periodic_alert_reload())
    asyncio.create_task(periodic_watch_reload())
    asyncio.create_task(periodic_status_push())
    asyncio.create_task(periodic_db_flush())
    asyncio.create_task(periodic_route_cache_save())
    asyncio.create_task(periodic_coverage_save())
    asyncio.create_task(periodic_summary())

    print(f"[HTTP] http://0.0.0.0:{HTTP_PORT}  [WS] ws://0.0.0.0:{WS_PORT}  [ADS-B] {TAR1090_URL}")

    # Readers
    await asyncio.gather(
        read_json_lines(ACARSHUB_HOST, ACARS_PORT, normalize_acars, "acars"),
        read_json_lines(ACARSHUB_HOST, VDLM2_PORT, normalize_vdlm2, "vdlm2"),
    )

# =========================
# Personal settings (my_settings.py)
# =========================
MY_SETTINGS_PATH = os.path.join(BASE_DIR, "my_settings.py")

def apply_my_settings():
    """Override any setting above with the values in my_settings.py (if present)."""
    if not os.path.isfile(MY_SETTINGS_PATH):
        print("[SETTINGS] No my_settings.py found; using the defaults in this file")
        return
    ns = {}
    try:
        with open(MY_SETTINGS_PATH, "r", encoding="utf-8") as f:
            exec(compile(f.read(), MY_SETTINGS_PATH, "exec"), ns)
    except Exception as e:
        print(f"[SETTINGS] my_settings.py has an error and was ignored: {e}")
        return
    g = globals()
    applied, unknown = [], []
    for k, v in ns.items():
        if not k.isupper() or k.startswith("_"):
            continue
        if k in g and not callable(g[k]):
            g[k] = v
            applied.append(k)
        else:
            unknown.append(k)
    # names only, never values (keys are secrets)
    print(f"[SETTINGS] Loaded my_settings.py: {', '.join(applied) or 'nothing to apply'}")
    if unknown:
        print(f"[SETTINGS] Ignored unknown names in my_settings.py (typo?): {', '.join(unknown)}")

apply_my_settings()

if __name__ == "__main__":
    import sys
    if "--test-pushover" in sys.argv:
        sys.exit(pushover_test())
    if "--test-summary" in sys.argv:
        load_alerts_history()
        db_init()
        sys.exit(0 if asyncio.run(send_summary(force=True)) else 1)
    asyncio.run(main())

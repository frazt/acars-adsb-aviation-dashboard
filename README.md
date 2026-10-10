# Live Aviation Dashboard

A single-file, real-time web dashboard for a home **ACARS / VDLM2 / ADS-B** receiving station.
It pairs the messages your decoders pick up with the aircraft your ADS-B receiver sees, and turns
them into a live feed, a map, trends, alerts and phone notifications.

Built to sit alongside the [sdr-enthusiasts](https://github.com/sdr-enthusiasts) Docker stack
(ACARS Hub, acarsdec, dumpvdl2, acars_router, tar1090 / ultrafeeder) and runs happily on the
same Raspberry Pi.

> _Add a screenshot here: `docs/screenshot.png`._

## Features

**Live feed**
- ACARS and VDLM2 messages as they arrive, with plain-English summaries of common message types
  (OOOI reports, position reports, weather requests, flight plans, ADS-C) and named message labels
- Messages matched to the ADS-B aircraft that sent them ("verified"), with distance and direction
- Filters, search, and a "hide noise" toggle for link tests and squitters

**Map**
- ADS-B aircraft coloured by altitude, helicopters with their own (spinning-rotor) icon
- Positions reported over ACARS / VDLM2 for aircraft your ADS-B can't see
- Click a plane for its route (from the aircraft's own messages or the adsbdb database, sanity-checked
  against its actual position), its flown trail and an altitude-coloured path
- Weather radar overlay with a 2-hour loop
- Coverage outlines: your farthest ACARS (yellow) and VDLM2 (purple) contact in every direction

**Flight timeline** — click any flight for its messages in order, OUT / OFF / ON / IN times with
block and air time, altitude profile and route.

**Trends** — messages per hour and per day, verified percentage, busiest hours, message types and
top airlines over 7 / 30 / 90 days (stored in a small SQLite database).

**Alerts**
- Keyword alerts (edit the list right in the Alerts tab), star alerts to keep them, reset the rest
- Emergency squawks (7700 / 7600 / 7500 and the ADS-B emergency flag): banner, flashing marker,
  high-priority phone alert
- Tracked aircraft list
- Takeoff / landing detector for airports you choose (rapid climb / descent near the field)

**Header** — local METAR weather (temperature, wind, altimeter, visibility, sky, flight category).

**Pushover notifications** (optional) — keyword alerts, emergencies and a nightly station summary.

## Requirements

- Python **3.10+** (Raspberry Pi OS Bookworm ships 3.11)
- The `websockets` package: `sudo apt install python3-websockets` or `pip install -r requirements.txt`
- **acars_router** with its TCP serve ports reachable (ACARS `15550`, VDLM2 `15555` by default)
- **tar1090** or **ultrafeeder** for ADS-B (`aircraft.json`). Turning on
  `TAR1090_ENABLE_AC_DB=true` gives aircraft types, which improves helicopter detection.

If acars_router runs in Docker, publish its TCP serve ports in your compose file:

```yaml
  acars_router:
    ports:
      - 15550:15550   # ACARS JSON over TCP
      - 15555:15555   # VDLM2 JSON over TCP
```

## Install

```bash
sudo mkdir -p /opt/aviation-dashboard && sudo chown $USER:$USER /opt/aviation-dashboard
git clone https://github.com/frazt/acars-adsb-aviation-dashboard.git /opt/aviation-dashboard
cd /opt/aviation-dashboard

cp my_settings.example.py my_settings.py
nano my_settings.py          # set HOME_LAT / HOME_LON, your hosts/ports, METAR station, keys

python3 live_aviation_dashboard.py
```

Open `http://<your-pi>:8000`. The dashboard also uses port `8765` (WebSocket) for live updates.

To start it at boot, see [`aviation-dashboard.service`](aviation-dashboard.service).

## Configuration

All settings live at the top of `live_aviation_dashboard.py`. **Don't edit them there** — put your
own values in `my_settings.py` (ignored by git), which overrides them. That way you can `git pull`
updates without losing anything. The log shows which settings were loaded (names only).

Commonly changed settings:

| Setting | What it does |
|---|---|
| `HOME_LAT`, `HOME_LON` | Your station location (required) |
| `ACARSHUB_HOST`, `ACARS_PORT`, `VDLM2_PORT` | Where acars_router serves ACARS / VDLM2 JSON over TCP |
| `TAR1090_URL` | Your tar1090 / ultrafeeder `aircraft.json` |
| `METAR_STATION` | ICAO code for the header weather strip (blank = off) |
| `AIRPORT_WATCH` | Airports for the takeoff / landing detector |
| `PUSHOVER_TOKEN`, `PUSHOVER_USER` | Turn on phone notifications |
| `SUMMARY_TIME`, `SUMMARY_ENABLED` | Nightly summary time (local, 24-hour) |
| `ROUTE_LOOKUP_ENABLED` | Set `False` to never contact adsbdb.com |

Keyword alerts go in `alerts.txt` (or edit them in the Alerts tab); tracked aircraft go in
`plane_alerts.txt`. See the `*.example.txt` files.

### Test commands

```bash
python3 live_aviation_dashboard.py --test-pushover   # send a test notification
python3 live_aviation_dashboard.py --test-summary    # build and send today's summary now
```

## Files it creates

All in the dashboard folder, all ignored by git:

| File | Contents |
|---|---|
| `state.json` | Counters (messages, verified, frequencies, airlines, distances) |
| `messages_recent.json`, `message_alerts.json` | Recent feed and alert history (starred alerts) |
| `message_log.db` | Message log for Trends (90 days) |
| `coverage.json` | Coverage outlines |
| `route_cache.json`, `airports.csv` | Route lookups and the airport list |

To reset counters, stop the dashboard and delete `state.json` (and `message_log.db` for Trends).
Alerts can be reset from the Alerts tab.

## Security

There is no login. Anyone who can open the page can reset alerts and edit alert words, so keep it on
your home network and don't expose port 8000 / 8765 to the internet.

## Data sources and credits

- Maps: [Leaflet](https://leafletjs.com/) and © [OpenStreetMap](https://www.openstreetmap.org/copyright) contributors
- Routes: [adsbdb.com](https://www.adsbdb.com/) (optional, cached)
- Airports: [OurAirports](https://ourairports.com/data/) (public domain), downloaded once
- Weather: [aviationweather.gov](https://aviationweather.gov/data/api/) (NOAA / NWS)
- Radar: [RainViewer](https://www.rainviewer.com/api.html)
- Notifications: [Pushover](https://pushover.net/)
- Decoding ecosystem: [sdr-enthusiasts](https://github.com/sdr-enthusiasts), acarsdec, dumpvdl2, libacars

Airline logos are not included. If you add your own PNGs under `static/airlines/` (see `LOGO_MAP`
in the code) they'll be used; otherwise the dashboard shows initials.

## License

MIT — see [LICENSE](LICENSE).

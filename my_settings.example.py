# Personal settings for the Live Aviation Dashboard.
#
#   cp my_settings.example.py my_settings.py
#
# then edit my_settings.py. It overrides the defaults at the top of live_aviation_dashboard.py,
# is ignored by git, and is never touched when you update the dashboard.
# Any setting from the top of live_aviation_dashboard.py can be put here.

# --- Home location (distances, map center, Nearby tab) -- required ---
HOME_LAT = 0.0
HOME_LON = 0.0

# --- Where the data comes from ---
ACARSHUB_HOST = "127.0.0.1"   # host running acars_router
ACARS_PORT    = 15550         # acars_router TCP serve port, ACARS
VDLM2_PORT    = 15555         # acars_router TCP serve port, VDLM2
TAR1090_URL   = "http://127.0.0.1:8080/data/aircraft.json"

# --- Weather strip in the header (nearest airport with a METAR; blank = off) ---
METAR_STATION = ""            # e.g. "KMCI"

# --- Takeoff / landing detector (optional) ---
# AIRPORT_WATCH = [
#     {"code": "MCI", "name": "Kansas City Intl", "lat": 39.2976, "lon": -94.7139, "elev": 1026},
# ]

# --- Pushover phone notifications (optional; https://pushover.net) ---
PUSHOVER_TOKEN = ""           # application API token
PUSHOVER_USER  = ""           # user key

# Optional extras:
# PUSHOVER_PRIORITY  = 1      # keyword alerts come through during quiet hours
# SUMMARY_TIME       = "21:00"
# SUMMARY_ENABLED    = False
# HTTP_PORT          = 8000

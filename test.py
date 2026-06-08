"""
streamlit_international.py
────────────────────────────────────────────────────────────────
International non-stop flight fare scraper → Google Sheets

Logic:
  • Scrapes 5 forward dates per route (24H, 48H, 7 Days, 15 Days, 30 Days)
  • Non-stop only — connecting flights are skipped
  • Per airline: finds the CHEAPEST flight, then captures ALL fare classes of that flight
  • Ex-PAK routes → prices stay in PKR
  • Ex-UAE routes → prices requested in AED  (currency=AED in URL)
  • Ex-KSA routes → prices requested in SAR  (currency=SAR in URL)
  • Results pushed to existing cells via a CONFIG sheet with columns:
      Route | Airline | Fare Name | Date Label | Fare Cell
    e.g.  ISB-RUH | PF | Nil Baggage | 24H | E5
"""

import asyncio
import json
import os
import pathlib
import random
import re
import subprocess
import sys
import threading
import time
import traceback
import urllib.parse
import warnings
from collections import defaultdict
from datetime import datetime, timedelta
from queue import Queue

import gspread
import streamlit as st
from google.oauth2.service_account import Credentials
from playwright.async_api import async_playwright
from playwright_stealth import Stealth

warnings.filterwarnings("ignore", category=DeprecationWarning)
if sys.platform == "win32":
    asyncio.set_event_loop_policy(asyncio.WindowsProactorEventLoopPolicy())

# ─────────────────────────────────────────────────────────────────────────────
# Playwright browser setup
# ─────────────────────────────────────────────────────────────────────────────
_browsers_dir = pathlib.Path(__file__).resolve().parent / ".playwright-browsers"
_browsers_dir.mkdir(parents=True, exist_ok=True)
os.environ["PLAYWRIGHT_BROWSERS_PATH"] = str(_browsers_dir)
_browser_install_lock = threading.Lock()


def _chromium_installed() -> bool:
    """Check any known location for a usable Chromium binary."""
    # 1. Check the configured browsers dir
    if _browsers_dir.is_dir():
        for name in ("chrome-headless-shell", "chrome", "chrome.exe",
                     "chrome-headless-shell.exe"):
            if any(_browsers_dir.rglob(name)):
                return True
    # 2. Also check the default Playwright cache (used when PLAYWRIGHT_BROWSERS_PATH
    #    is not honoured, e.g. on some Windows setups)
    default_cache = pathlib.Path.home() / "AppData" / "Local" / "ms-playwright"
    if default_cache.is_dir():
        for name in ("chrome-headless-shell.exe", "chrome.exe"):
            if any(default_cache.rglob(name)):
                return True
    return False


def ensure_playwright_browsers() -> None:
    if _chromium_installed():
        return
    with _browser_install_lock:
        if _chromium_installed():
            return
        print("⏳ Downloading Playwright Chromium (first run ~1-2 min)...")
        proc = subprocess.run(
            [sys.executable, "-m", "playwright", "install", "chromium"],
            env={**os.environ, "PLAYWRIGHT_BROWSERS_PATH": str(_browsers_dir)},
            capture_output=True, text=True, timeout=600,
        )
        if proc.stdout:
            print(proc.stdout.strip())
        if proc.returncode != 0:
            raise RuntimeError(
                f"playwright install failed:\n{proc.stderr}\n{proc.stdout}"
            )
        if not _chromium_installed():
            raise RuntimeError(f"Chromium still missing after install.")
        print("✅ Playwright Chromium ready.\n")


# ─────────────────────────────────────────────────────────────────────────────
# Persistent queues
# ─────────────────────────────────────────────────────────────────────────────
if "intl_log_queue" not in st.session_state:
    st.session_state.intl_log_queue = Queue()
if "intl_data_queue" not in st.session_state:
    st.session_state.intl_data_queue = Queue()

log_queue  = st.session_state.intl_log_queue
data_queue = st.session_state.intl_data_queue

original_print = print


def log_print(*args, **kwargs):
    sep = kwargs.get("sep", " ")
    end = kwargs.get("end", "\n")
    message = sep.join(str(a) for a in args) + end
    log_queue.put(message)
    original_print(message, file=sys.__stdout__)


print = log_print

# ─────────────────────────────────────────────────────────────────────────────
# Route & date config
# ─────────────────────────────────────────────────────────────────────────────
AIRPORT_NAMES = {
    "ISB": "Islamabad", "KHI": "Karachi",   "LHE": "Lahore",
    "DXB": "Dubai",     "AUH": "Abu Dhabi", "SHJ": "Sharjah",
    "RUH": "Riyadh",    "JED": "Jeddah",    "DMM": "Dammam", "MED": "Medina",
}

HEADLESS = st.secrets.get("HEADLESS", True)

# Date offsets and their labels (must match CONFIG sheet exactly)
DATE_OFFSETS = [1, 2, 7, 15, 30]
DATE_LABELS  = ["24H", "48H", "7 Days", "15 Days", "30 Days"]

# UAE region ─ ex-PAK scraped in PKR, ex-UAE scraped in AED
# UAE region ─ only ISB ↔ DXB
UAE_SECTORS = [
    # Ex-PAK → UAE  (PKR)
    ("ISB", "DXB", "PKR"), ("LHE", "DXB", "PKR"), ("KHI", "DXB", "PKR"), ("MUX", "DXB", "PKR"),
    ("ISB", "AUH", "PKR"), ("LHE", "AUH", "PKR"),
    ("ISB", "SHJ", "PKR"), ("LHE", "SHJ", "PKR"), ("MUX", "SHJ", "PKR"),
    # Ex-UAE → PAK  (AED)
    ("DXB", "ISB", "AED"), ("DXB", "LHE", "AED"), ("DXB", "KHI", "AED"), ("DXB", "MUX", "AED"),
    ("AUH", "ISB", "AED"), ("AUH", "LHE", "AED"), 
    ("SHJ", "ISB", "AED"), ("SHJ", "LHE", "AED"), ("SHJ", "MUX", "AED"),
]

# KSA region ─ ex-PAK scraped in PKR, ex-KSA scraped in SAR
KSA_SECTORS = [
    # Ex-PAK → KSA  (PKR)
    ("ISB", "RUH", "PKR"), ("LHE", "RUH", "PKR"), 
    ("ISB", "JED", "PKR"), ("LHE", "JED", "PKR"), ("KHI", "JED", "PKR"),
    ("MUX", "JED", "PKR"), 
    # Ex-KSA → PAK  (SAR)
    ("RUH", "ISB", "SAR"), ("RUH", "LHE", "SAR"), 
    ("JED", "ISB", "SAR"), ("JED", "LHE", "SAR"), ("JED", "KHI", "SAR"),
    ("JED", "MUX", "SAR"), 
]

STALL_SECONDS  = 120
STABLE_SECONDS = 5
RESTART_DELAY  = 10

# ─────────────────────────────────────────────────────────────────────────────
# Browser / JS hooks
# ─────────────────────────────────────────────────────────────────────────────
HOOK_JS = """
window.__allFlightBatches = [];
const _orig = JSON.parse;
JSON.parse = function(...args) {
    const result = _orig.apply(this, args);
    try {
        const s = JSON.stringify(result);
        if (s.includes('"flights"') && s.includes('"flight_number"'))
            window.__allFlightBatches.push(result);
    } catch(e) {}
    return result;
};
"""

COUNT_JS = """
() => {
    let total = 0;
    for (const batch of window.__allFlightBatches) {
        const lists = (batch.data && batch.data.flights)
            ? batch.data.flights : (batch.flights || []);
        for (const fl of lists)
            total += Array.isArray(fl) ? fl.length : 1;
    }
    return total;
}
"""


async def open_browser(p, worker_id: int = 0):
    """Each worker gets an isolated Chrome profile so sessions never collide."""
    context = await p.chromium.launch_persistent_context(
        user_data_dir=f"/tmp/chrome_profile_intl_w{worker_id}",
        headless=HEADLESS,
        no_viewport=True,
        args=["--disable-blink-features=AutomationControlled", "--start-maximized"],
        user_agent=(
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/120.0.0.0 Safari/537.36"
        ),
    )
    page = context.pages[0] if context.pages else await context.new_page()
    await page.add_init_script(HOOK_JS)
    return context, page


# ─────────────────────────────────────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────────────────────────────────────
def build_url(origin: str, dest: str, date: str, currency: str) -> str:
    cabin = urllib.parse.quote(json.dumps({"code": "Y", "label": "Economy"}))
    legs  = urllib.parse.quote(json.dumps([{
        "departureDate":   date,
        "origin":          origin,
        "destination":     dest,
        "originName":      AIRPORT_NAMES.get(origin, origin),
        "destinationName": AIRPORT_NAMES.get(dest, dest),
    }]))[3:-3]
    pax = urllib.parse.quote(json.dumps({"numAdult": 1, "numChild": 0, "numInfant": 0}))
    url = (
        f"https://www.sastaticket.pk/air/search"
        f"?cabinClass={cabin}&legs[]={legs}&routeType=ONEWAY"
        f"&travelerCount={pax}&sortBy=cheapest"
    )
    if currency.upper() != "PKR":
        url += f"&currency={currency.upper()}"
    return url


def is_nonstop(flight: dict) -> bool:
    legs = flight.get("legs") or []
    if len(legs) != 1:
        return False
    segs = legs[0].get("segments") or []
    if len(segs) != 1:
        return False
    leg = legs[0]
    for field in ("stops", "stop_count", "number_of_stops", "num_stops"):
        for obj in (leg, flight):
            if field not in obj:
                continue
            val = obj[field]
            if val not in (0, "0", None, False, ""):
                return False
    label = str(
        leg.get("stop_label") or leg.get("stops_text") or leg.get("stop_info") or ""
    ).lower()
    if label and any(w in label for w in ("stop", "layover", "connect", "via ")):
        if not any(w in label for w in ("non-stop", "nonstop", "direct", "0 stop")):
            return False
    return True


def dep_time(flight: dict) -> str:
    try:
        seg = flight["legs"][0]["segments"][0]
        raw = (
            seg.get("departure_datetime") or seg.get("departure_time")
            or seg.get("dep_time") or seg.get("departure") or ""
        )
        if not raw:
            return "N/A"
        m = re.search(r"T(\d{2}:\d{2})", str(raw))
        if m:
            h, mn = map(int, m.group(1).split(":"))
            return f"{h % 12 or 12}:{mn:02d} {'AM' if h < 12 else 'PM'}"
        return str(raw)
    except Exception:
        return "N/A"


def airline_code(flight: dict) -> str:
    try:
        return flight["legs"][0]["segments"][0]["operating_airline"]["code"].upper()
    except Exception:
        return "??"


# ─────────────────────────────────────────────────────────────────────────────
# Core scrape: one (origin, dest, date, currency)
#
# Returns: { airline_code: { fare_name: price, "__time__": dep_time } }
#   → cheapest flight per airline, all fare classes of that flight
# ─────────────────────────────────────────────────────────────────────────────
async def scrape_one(page, origin: str, dest: str, date: str, currency: str) -> dict | None:
    """
    Returns None  → stalled (browser restart needed)
    Returns {}    → no data / no non-stop flights
    Returns dict  → { airline: { fare_name: price, "__time__": str } }
    Prices are converted from PKR to the requested currency using the exchange rate.
    """
    await page.evaluate("window.__allFlightBatches = []")
    await page.goto(build_url(origin, dest, date, currency), wait_until="commit")
    await page.wait_for_timeout(3000)

    try:
        btn = page.locator('button:has-text("Stay on the web")')
        if await btn.is_visible():
            await btn.click()
    except Exception:
        pass

    last_count   = -1
    stable_ticks = 0
    zero_ticks   = 0

    for _ in range(STALL_SECONDS + STABLE_SECONDS + 10):
        await asyncio.sleep(1)
        count = await page.evaluate(COUNT_JS)

        if count == 0:
            zero_ticks += 1
            if zero_ticks >= STALL_SECONDS:
                print(f"      ⚠️  Stalled — no flights for {STALL_SECONDS}s")
                return None
        else:
            zero_ticks = 0

        if count > 0 and count == last_count:
            stable_ticks += 1
            if stable_ticks >= STABLE_SECONDS:
                nb = await page.evaluate("window.__allFlightBatches.length")
                print(f"      ✅ Stable — {count} flights / {nb} batch(es)")
                break
        else:
            if count != last_count:
                nb = await page.evaluate("window.__allFlightBatches.length")
                print(f"      📦 {count} flights / {nb} batch(es)...")
            stable_ticks = 0
            last_count   = count

    all_batches = await page.evaluate("window.__allFlightBatches")
    if not all_batches:
        return {}

    # De-duplicate raw flights
    all_flights, seen = [], set()
    for batch in all_batches:
        lists = batch.get("data", {}).get("flights") or batch.get("flights") or []
        for item in lists:
            for fl in (item if isinstance(item, list) else [item]):
                h = fl.get("hash") or json.dumps(fl, sort_keys=True)[:80]
                if h not in seen:
                    seen.add(h)
                    all_flights.append(fl)

    print(f"      ✈️  {len(all_flights)} unique flights — filtering non-stop...")

    # Per airline: track the cheapest-flight's cheapest fare price
    best_per_airline: dict[str, dict] = {}
    skipped = 0

    for fl in all_flights:
        if not is_nonstop(fl):
            skipped += 1
            continue

        al = airline_code(fl)

        # Find cheapest fare option for this flight
        min_price = None
        for fo in fl.get("fare_options", []):
            p = (
                fo.get("price", {}).get("selling_fare")
                or fo.get("selling_fare")
                or fo.get("price") or 0
            )
            if isinstance(p, (int, float)) and p > 0:
                if min_price is None or p < min_price:
                    min_price = p

        if min_price is None:
            continue

        # Keep only the cheapest flight per airline
        if al not in best_per_airline or min_price < best_per_airline[al]["min_price"]:
            best_per_airline[al] = {"min_price": min_price, "flight": fl}

    if skipped:
        print(f"      ⏭️  Skipped {skipped} connecting flight(s)")

    # Now extract ALL fare classes for each airline's cheapest flight,
    # converting prices from PKR to the target currency using exchange_rate.
    result = {}
    for al, info in best_per_airline.items():
        fl = info["flight"]
        t  = dep_time(fl)

        # --- Exchange rate retrieval ---
        exchange_rates = fl.get("meta", {}).get("exchange_rate", {})
        rate = 1.0
        if currency != "PKR":
            # Try to get the rate for the target currency
            rate = exchange_rates.get(currency)
            if not rate or rate <= 0:
                # Some flights might not have the rate directly; fallback to manual
                # For SAR, we can also use sar_to_pkr_rate from provider meta
                if currency == "SAR":
                    provider_meta = fl.get("fare_options", [{}])[0].get("price", {}).get("meta", {})
                    sar_rate = provider_meta.get("sar_to_pkr_rate")
                    if sar_rate and sar_rate > 0:
                        rate = 1.0 / sar_rate   # because sar_to_pkr_rate means 1 SAR = X PKR, so PKR to SAR = 1/X
                if not rate or rate <= 0:
                    print(f"      ⚠️  Exchange rate for {currency} not found, keeping PKR")
                    rate = 1.0
        # -------------------------------

        fares = {}
        for fo in fl.get("fare_options", []):
            fname = (fo.get("fare_name") or "").strip()
            p = (
                fo.get("price", {}).get("selling_fare")
                or fo.get("selling_fare")
                or fo.get("price") or 0
            )
            if fname and isinstance(p, (int, float)) and p > 0:
                converted = round(p * rate)
                if fname not in fares or converted < fares[fname]:
                    fares[fname] = converted

        if fares:
            result[al] = {"__time__": t, **fares}
            min_fare = min(v for v in fares.values())
            print(f"        → {al}  cheapest={min_fare} {currency}  "
                  f"fares=[{', '.join(fares.keys())}]  {t}")

    return result

# ─────────────────────────────────────────────────────────────────────────────
# Parallel scraping architecture
#
# scrape_worker       – one async coroutine per browser worker
# scrape_all_parallel – spawns N workers, each in its own Playwright context
# scrape_all          – legacy alias (n_workers=1)
# ─────────────────────────────────────────────────────────────────────────────
async def scrape_worker(
    worker_id: int,
    sectors_chunk: list,
    shared_results: dict,
    results_lock: asyncio.Lock,
    total_tasks: int,
    completed_counter: list,   # [int] — shared mutable counter via list
) -> None:
    """
    Runs one isolated Playwright/Chromium instance for the given sector chunk.
    Each worker writes into shared_results under results_lock, and pushes
    live rows to data_queue / log lines to log_queue as usual.
    """
    tag = f"[W{worker_id}]"

    async with Stealth().use_async(async_playwright()) as p:
        context, page = await open_browser(p, worker_id)
        retries = 0

        for (origin, dest, currency) in sectors_chunk:
            for offset, label in zip(DATE_OFFSETS, DATE_LABELS):
                target_date = (datetime.now() + timedelta(days=offset)).strftime("%Y-%m-%d")
                completed_counter[0] += 1
                route_key = f"{origin}-{dest}"
                print(f"\n  {tag} [{completed_counter[0]}/{total_tasks}] "
                      f"{route_key} – {label} ({target_date})  [{currency}]")

                while True:
                    try:
                        data = await scrape_one(page, origin, dest, target_date, currency)
                    except Exception as e:
                        print(f"      {tag} ❌ Exception: {e}")
                        data = {}

                    if data is None:
                        retries += 1
                        if retries >= 3:
                            print(f"      {tag} ❌ Max retries — skipping {route_key} {label}")
                            data = {}
                            retries = 0
                            break
                        print(f"      {tag} 🔁 Retry {retries}/3 — restarting browser...")
                        try:
                            await context.close()
                        except Exception:
                            pass
                        await asyncio.sleep(RESTART_DELAY)
                        context, page = await open_browser(p, worker_id)
                        continue
                    else:
                        retries = 0
                        break

                async with results_lock:
                    shared_results[(origin, dest, label)] = data

                # Push to live UI
                for al, fare_dict in (data or {}).items():
                    for fname, price in fare_dict.items():
                        if fname == "__time__":
                            continue
                        data_queue.put({
                            "route":    route_key,
                            "airline":  al,
                            "fare":     fname,
                            "date":     label,
                            "price":    price,
                            "currency": currency,
                            "time":     fare_dict.get("__time__", ""),
                            "worker":   worker_id,
                        })

                remaining = total_tasks - completed_counter[0]
                if remaining > 0:
                    delay = random.uniform(20, 40)
                    print(f"      {tag} 💤 Sleeping {delay:.1f}s...")
                    await asyncio.sleep(delay)

        try:
            await context.close()
        except Exception:
            pass


async def scrape_all_parallel(sectors: list, n_workers: int = 4) -> dict:
    """
    Splits `sectors` into `n_workers` chunks (round-robin) and runs each
    chunk in its own Playwright instance concurrently via asyncio.gather.
    Returns a merged results dict identical in shape to the old scrape_all().
    """
    n_workers = max(1, min(n_workers, len(sectors)))

    # Round-robin assignment: sector i → worker (i % n_workers)
    chunks: list[list] = [[] for _ in range(n_workers)]
    for i, sector in enumerate(sectors):
        chunks[i % n_workers].append(sector)

    total_tasks       = len(sectors) * len(DATE_OFFSETS)
    shared_results: dict = {}
    results_lock      = asyncio.Lock()
    completed_counter = [0]   # shared via mutable list

    print(f"  🚀 Launching {n_workers} parallel browser(s) — "
          f"{len(sectors)} sectors × {len(DATE_OFFSETS)} dates = {total_tasks} tasks")
    for i, chunk in enumerate(chunks):
        if chunk:
            routes = ", ".join(f"{o}-{d}" for o, d, _ in chunk)
            print(f"     W{i}: {len(chunk)} sector(s) → {routes}")
    print()

    await asyncio.gather(*[
        scrape_worker(
            worker_id=i,
            sectors_chunk=chunk,
            shared_results=shared_results,
            results_lock=results_lock,
            total_tasks=total_tasks,
            completed_counter=completed_counter,
        )
        for i, chunk in enumerate(chunks)
        if chunk
    ])

    return shared_results


async def scrape_all(sectors: list) -> dict:
    """Legacy single-worker alias."""
    return await scrape_all_parallel(sectors, n_workers=1)



# ─────────────────────────────────────────────────────────────────────────────
# Google Sheets push
#
# CONFIG sheet columns (exact header names):
#   Route       e.g.  ISB-RUH
#   Airline     e.g.  PF          (operating airline code)
#   Fare Name   e.g.  Nil Baggage (must match API fare_name exactly)
#   Date Label  e.g.  24H         (must match DATE_LABELS exactly)
#   Fare Cell   e.g.  E5          (cell in target worksheet)
#
# One CONFIG row per (route, airline, fare_name, date_label) combination.
# ─────────────────────────────────────────────────────────────────────────────
def push_to_sheets(results: dict, worksheet_name: str,
                   spreadsheet_id: str, config_sheet: str) -> dict:
    creds_json = st.secrets["gcp_service_account"]
    creds = Credentials.from_service_account_info(
        creds_json,
        scopes=["https://www.googleapis.com/auth/spreadsheets",
                "https://www.googleapis.com/auth/drive"],
    )
    client      = gspread.authorize(creds)
    spreadsheet = client.open_by_key(spreadsheet_id)

    print(f"  📋 Reading config sheet: '{config_sheet}'")
    config_ws = spreadsheet.worksheet(config_sheet)

    try:
        target_ws = spreadsheet.worksheet(worksheet_name)
    except gspread.exceptions.WorksheetNotFound:
        target_ws = spreadsheet.add_worksheet(title=worksheet_name, rows=1000, cols=100)
        print(f"  📄 Created worksheet '{worksheet_name}'")

    # Build mapping: (route, airline, fare_name, date_label) → fare_cell
    mapping: dict[tuple, str] = {}
    for row in config_ws.get_all_records():
        route      = str(row.get("Route", "")).replace("→", "-").strip().upper()
        airline    = str(row.get("Airline", "")).strip().upper()
        fare_name  = str(row.get("Fare Name", "")).strip()
        date_label = str(row.get("Date Label", "")).strip()
        fare_cell  = str(row.get("Fare Cell", "")).strip()

        if not all([route, airline, fare_name, date_label, fare_cell]):
            continue

        mapping[(route, airline, fare_name, date_label)] = fare_cell

    print(f"  📋 Config loaded — {len(mapping)} cell mappings")

    batch_requests = []
    pasted: list[dict]   = []
    unmapped: list[dict] = []

    for (origin, dest, date_label), airline_data in results.items():
        route_key = f"{origin}-{dest}"

        for airline, fare_dict in airline_data.items():
            dep = fare_dict.get("__time__", "")

            for fare_name, price in fare_dict.items():
                if fare_name == "__time__":
                    continue

                key = (route_key, airline, fare_name, date_label)
                cell = mapping.get(key)

                if not cell:
                    unmapped.append({
                        "route": route_key, "airline": airline,
                        "fare":  fare_name, "date": date_label,
                        "price": int(price), "time": dep,
                    })
                    continue

                batch_requests.append({"range": cell, "values": [[int(price)]]})
                pasted.append({
                    "route": route_key, "airline": airline,
                    "fare":  fare_name, "date": date_label,
                    "price": int(price), "cell": cell, "time": dep,
                })
                print(f"  → {route_key} | {airline} | {fare_name:<20} | "
                      f"{date_label:<8} | {int(price):>7} → {cell}")

    # Timestamp
    now = datetime.now()
    h   = now.hour % 12 or 12
    batch_requests.append({
        "range": "A1",
        "values": [[f"Updated {now.strftime('%d %b %Y')} at "
                    f"{h}:{now.strftime('%M')} {now.strftime('%p')}"]],
    })

    if batch_requests:
        print(f"\n  Sending {len(batch_requests)} cell updates...")
        target_ws.batch_update(batch_requests)
        print("  ✅ Google Sheet updated.")
    else:
        print("  ⚠️  No updates to send.")

    print("\n" + "═" * 60)
    print(f"  ✅ Pasted : {len(pasted)} values")
    print(f"  ⚠️  Unmapped: {len(unmapped)} values")
    if unmapped:
        print("  Add these to CONFIG to paste them next run:")
        for r in sorted(unmapped, key=lambda x: (x["route"], x["airline"], x["fare"], x["date"])):
            print(f"     {r['route']} | {r['airline']} | {r['fare']:<20} | "
                  f"{r['date']:<8} | {r['price']}")
    print("═" * 60)

    return {"pasted": pasted, "unmapped": unmapped}


# ─────────────────────────────────────────────────────────────────────────────
# Background thread
# ─────────────────────────────────────────────────────────────────────────────
def run_scrape_thread(region: str, worksheet_name: str,
                      spreadsheet_id: str, config_sheet: str,
                      n_workers: int = 4):
    try:
        from streamlit.runtime.scriptrunner import add_script_run_ctx
        ctx = st.runtime.scriptrunner.get_script_run_ctx()
        if ctx:
            add_script_run_ctx(threading.current_thread(), ctx)
    except Exception:
        pass

    try:
        sectors = UAE_SECTORS if region == "UAE" else KSA_SECTORS

        print("═" * 60)
        print("  SkySync Pro — Parallel Scraper")
        print("═" * 60)
        print(f"  Region   : {region}")
        print(f"  Sectors  : {len(sectors)}")
        print(f"  Workers  : {n_workers}")
        print(f"  Dates    : {', '.join(DATE_LABELS)}")
        print(f"  Config   : {config_sheet}")
        print("═" * 60 + "\n")

        ensure_playwright_browsers()
        results = asyncio.run(scrape_all_parallel(sectors, n_workers=n_workers))

        if not results:
            print("\n⚠️  No data collected.")
        else:
            total_fares = sum(
                len([k for k in fd if k != "__time__"])
                for ad in results.values()
                for fd in ad.values()
            )
            print(f"\n📋 Pushing {total_fares} fare values to "
                  f"\'{worksheet_name}\'...")
            sheet_result = push_to_sheets(
                results, worksheet_name, spreadsheet_id, config_sheet
            )
            st.session_state["intl_pasted"]   = sheet_result["pasted"]
            st.session_state["intl_unmapped"] = sheet_result["unmapped"]
            print("\n🏁 All done!")

    except Exception:
        print("=" * 60)
        print("❌ EXCEPTION IN SCRAPER")
        print("=" * 60)
        traceback.print_exc(file=sys.stderr)
        log_queue.put(traceback.format_exc())
    finally:
        st.session_state["intl_scraping_done"] = True


# ─────────────────────────────────────────────────────────────────────────────
# Streamlit UI
# ─────────────────────────────────────────────────────────────────────────────
_CSS = """
@import url('https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700;800&family=JetBrains+Mono:wght@400;500&display=swap');

/* ── Base ── */
.stApp { background:#f0f4f8; color:#1e293b; font-family:'Inter',sans-serif; }
.block-container { padding-top:1.2rem; max-width:1280px; }

/* ── Hero ── */
.neo-hero { text-align:center; padding:1.8rem 1rem 0.8rem; margin-bottom:0.5rem; }
.neo-hero h1 { font-size:clamp(1.6rem,4vw,2.4rem); font-weight:800; letter-spacing:-0.03em; color:#0f172a; margin:0; }
.neo-hero h1 span { background:linear-gradient(135deg,#2563eb 0%,#3b82f6 50%,#0ea5e9 100%); -webkit-background-clip:text; -webkit-text-fill-color:transparent; background-clip:text; }
.neo-hero p { font-size:0.83rem; color:#64748b; margin-top:0.4rem; }

/* ── Status pill ── */
.status-pill { display:inline-flex; align-items:center; gap:0.4rem; font-size:0.68rem; font-weight:700; letter-spacing:0.1em; padding:0.3rem 1.1rem; border-radius:999px; border:1.5px solid; text-transform:uppercase; }
.status-idle { color:#64748b; border-color:#cbd5e1; background:#f8fafc; }
.status-scan { color:#1d4ed8; border-color:#93c5fd; background:#eff6ff; animation:pulse-scan 1.8s ease-in-out infinite; }
.status-done { color:#15803d; border-color:#86efac; background:#f0fdf4; }
@keyframes pulse-scan {
    0%,100% { box-shadow:0 0 0 0 rgba(59,130,246,0.25); }
    50%      { box-shadow:0 0 0 8px rgba(59,130,246,0); }
}

/* ── Stat cards ── */
.neo-card { background:white; border-radius:16px; padding:1.2rem 0.8rem 1rem; box-shadow:0 1px 3px rgba(0,0,0,0.06),0 4px 16px rgba(0,0,0,0.05); text-align:center; border:1px solid #e2e8f0; transition:box-shadow 0.2s; }
.neo-card:hover { box-shadow:0 4px 24px rgba(37,99,235,0.1); }
.neo-card h3 { font-size:0.62rem; font-weight:700; letter-spacing:0.12em; color:#94a3b8; text-transform:uppercase; margin:0 0 0.5rem 0; }
.neo-card .val { font-size:1.7rem; font-weight:800; color:#0f172a; letter-spacing:-0.02em; line-height:1; }
.neo-card .sub { font-size:0.65rem; color:#94a3b8; margin-top:0.35rem; font-weight:500; }

/* ── Section title ── */
.neo-section-title { font-size:0.62rem; font-weight:700; letter-spacing:0.18em; color:#3b82f6; text-transform:uppercase; margin:1.4rem 0 0.5rem; }

/* ── Terminal ── */
.neo-terminal { font-family:'JetBrains Mono','Courier New',monospace; font-size:0.73rem; line-height:1.6; background:#fafbfc; border:1px solid #e2e8f0; border-radius:14px; padding:1rem 1.1rem; color:#1e293b; max-height:360px; overflow-y:auto; white-space:pre-wrap; word-break:break-word; scroll-behavior:smooth; }

/* ── Controls ── */
div[data-testid="stTextInput"] label { font-size:0.65rem !important; font-weight:700 !important; color:#64748b !important; text-transform:uppercase; letter-spacing:0.1em; }
div[data-testid="stTextInput"] input { background:white !important; border:1.5px solid #e2e8f0 !important; border-radius:10px !important; color:#0f172a !important; font-size:0.88rem !important; }
div[data-testid="stTextInput"] input:focus { border-color:#3b82f6 !important; box-shadow:0 0 0 3px rgba(59,130,246,0.1) !important; }

/* ── Buttons ── */
.stButton > button { font-weight:700 !important; font-size:0.82rem !important; background:linear-gradient(135deg,#2563eb,#3b82f6) !important; border:none !important; border-radius:10px !important; padding:0.6rem 1.4rem !important; color:white !important; letter-spacing:0.02em !important; transition:all 0.2s !important; box-shadow:0 2px 8px rgba(37,99,235,0.3) !important; }
.stButton > button:hover:not(:disabled) { background:linear-gradient(135deg,#1d4ed8,#2563eb) !important; box-shadow:0 4px 16px rgba(37,99,235,0.4) !important; transform:translateY(-1px); }
.stButton > button:disabled { background:#e2e8f0 !important; color:#94a3b8 !important; box-shadow:none !important; }

/* ── Dataframe ── */
div[data-testid="stDataFrame"] { border:1px solid #e2e8f0; border-radius:14px; overflow:hidden; background:white; box-shadow:0 1px 6px rgba(0,0,0,0.04); }

/* ── Banners ── */
.neo-banner-ok { background:linear-gradient(135deg,#f0fdf4,#dcfce7); border:1.5px solid #86efac; border-radius:14px; padding:1rem 1.4rem; text-align:center; color:#15803d; font-weight:600; font-size:0.9rem; margin:1rem 0; }
.neo-banner-wait { background:white; border:1.5px dashed #cbd5e1; border-radius:14px; padding:2rem; text-align:center; color:#94a3b8; font-size:0.85rem; }

/* ── Progress bar ── */
div[data-testid="stProgress"] > div > div { background:linear-gradient(90deg,#2563eb,#60a5fa) !important; border-radius:999px !important; }

/* ── Radio ── */
div[data-testid="stRadio"] label { font-size:0.85rem !important; font-weight:500 !important; }
"""


st.set_page_config(
    page_title="SkySync Pro — Fare Intelligence",
    page_icon="✈️",
    layout="wide",
    initial_sidebar_state="collapsed",
)
st.markdown(f"<style>{_CSS}</style>", unsafe_allow_html=True)
st.markdown(
    '<div class="neo-hero"><h1>✈ <span>SKYSYNC PRO</span></h1>'
    '<p>UAE &amp; KSA fare intelligence — non-stop only · all classes → Google Sheets</p></div>',
    unsafe_allow_html=True,
)

# Session state
for _k, _v in [
    ("intl_scraping_started", False), ("intl_scraping_done", False),
    ("intl_log_text", ""),            ("intl_fare_rows", []),
    ("intl_pasted", []),              ("intl_unmapped", []),
]:
    if _k not in st.session_state:
        st.session_state[_k] = _v


def _status():
    if st.session_state.intl_scraping_done:    return "done"
    if st.session_state.intl_scraping_started: return "scan"
    return "idle"


def _status_html():
    m = {"idle": ("STANDBY","status-pill status-idle"),
         "scan": ("SCANNING","status-pill status-scan"),
         "done": ("COMPLETE","status-pill status-done")}
    t, c = m[_status()]
    return f'<span class="{c}">{t}</span>'


st.markdown(
    f'<div style="text-align:center;margin-bottom:1.5rem;">{_status_html()}</div>',
    unsafe_allow_html=True,
)

# ── Stats row ────────────────────────────────────────────────────────────────
def _stats_row(region: str):
    n_fares   = len(st.session_state.intl_fare_rows)
    n_sectors = len(UAE_SECTORS if region == "UAE" else KSA_SECTORS)
    n_workers = st.session_state.get("_intl_n_workers", 1)
    c1, c2, c3, c4, c5 = st.columns(5)
    cards = [
        ("Region",   region,               "selected"),
        ("Sectors",  str(n_sectors),       "routes to scrape"),
        ("Workers",  str(n_workers),       "parallel browsers"),
        ("Dates",    str(len(DATE_LABELS)),"per sector"),
        ("Fares",    str(n_fares),         "captured so far"),
    ]
    for col, (title, val, sub) in zip((c1, c2, c3, c4, c5), cards):
        with col:
            st.markdown(
                f'<div class="neo-card"><h3>{title}</h3>'
                f'<div class="val">{val}</div>'
                f'<div class="sub">{sub}</div></div>',
                unsafe_allow_html=True,
            )


# ── Controls ─────────────────────────────────────────────────────────────────
st.markdown(
    '<p class="neo-section-title">Mission control</p>',
    unsafe_allow_html=True,
)

col_region, col_tab, col_workers, col_btn = st.columns([1, 2, 1, 1], gap="large")

with col_region:
    region = st.radio(
        "Region",
        ["UAE", "KSA"],
        horizontal=True,
        label_visibility="collapsed",
        disabled=st.session_state.intl_scraping_started,
    )

with col_tab:
    worksheet_name = st.text_input(
        "Worksheet tab",
        placeholder="e.g. May-20",
        label_visibility="visible",
    )

    _region_key    = region.lower()
    config_sheet   = st.secrets.get(f"intl_{_region_key}_config_sheet",
                                     f"CONFIG_{region}")
    spreadsheet_id = st.secrets.get(f"intl_{_region_key}_spreadsheet_id", "")

    if not spreadsheet_id:
        st.warning(
            f"Add `intl_{_region_key}_spreadsheet_id` to your secrets.toml.",
            icon="⚠️",
        )

    _n_sectors = len(UAE_SECTORS if region == "UAE" else KSA_SECTORS)
    st.caption(
        f"Config: `{config_sheet}` · "
        f"Non-stop only · All fare classes · "
        f"Ex-PAK fares in PKR, ex-UAE in AED, ex-KSA in SAR"
    )

with col_workers:
    _max_workers = min(_n_sectors, 8)
    n_workers = st.slider(
        "Parallel workers",
        min_value=1,
        max_value=_max_workers,
        value=min(4, _max_workers),
        step=1,
        disabled=st.session_state.intl_scraping_started,
        help=(
            f"Splits {_n_sectors} sectors across N browser tabs running simultaneously. "
            f"Each worker handles ~{max(1, _n_sectors // min(4, _max_workers))} sectors."
        ),
    )
    # Show the split preview
    _chunk_sizes = [len(list(range(i, _n_sectors, n_workers))) for i in range(n_workers)]
    st.caption(" · ".join(f"W{i}: {s}s" for i, s in enumerate(_chunk_sizes)))

with col_btn:
    st.markdown("<div style='height:1.9rem'></div>", unsafe_allow_html=True)
    start_button = st.button(
        "▶ Start scan",
        disabled=(
            not worksheet_name
            or not spreadsheet_id
            or st.session_state.intl_scraping_started
        ),
        use_container_width=True,
    )

_stats_row(region)

# ── Start ────────────────────────────────────────────────────────────────────
if start_button and not st.session_state.intl_scraping_started:
    st.session_state.intl_scraping_started = True
    st.session_state.intl_scraping_done    = False
    while not log_queue.empty():  log_queue.get()
    while not data_queue.empty(): data_queue.get()
    st.session_state.intl_log_text  = ""
    st.session_state.intl_fare_rows = []
    st.session_state.intl_pasted    = []
    st.session_state.intl_unmapped  = []

    st.session_state["_intl_region"]         = region
    st.session_state["_intl_worksheet"]      = worksheet_name
    st.session_state["_intl_spreadsheet_id"] = spreadsheet_id
    st.session_state["_intl_config_sheet"]   = config_sheet
    st.session_state["_intl_n_workers"]      = n_workers

    thread = threading.Thread(
        target=run_scrape_thread,
        args=(region, worksheet_name, spreadsheet_id, config_sheet),
        kwargs={"n_workers": n_workers},
        daemon=True,
    )
    thread.start()
    st.rerun()


# ── Live panel (fragment = only this section reruns, no page scroll reset) ───
@st.fragment(run_every=0.5)
def _live_panel():
    """Drains queues and redraws the dynamic portion without touching the page scroll."""
    if st.session_state.intl_scraping_started:
        # Drain log queue
        lines = []
        while not log_queue.empty():
            lines.append(log_queue.get())
        if lines:
            st.session_state.intl_log_text += "".join(lines)

        # Drain data queue
        while not data_queue.empty():
            st.session_state.intl_fare_rows.append(data_queue.get())

        # Progress bar (only while running)
        if not st.session_state.intl_scraping_done:
            n_sectors = len(
                UAE_SECTORS if st.session_state.get("_intl_region") == "UAE"
                else KSA_SECTORS
            )
            total = n_sectors * len(DATE_OFFSETS)
            done  = len(set(
                (r["route"], r["date"])
                for r in st.session_state.intl_fare_rows
            ))
            st.progress(
                min(1.0, done / max(total, 1)),
                text=f"Scanning… {done}/{total} route-date combinations",
            )

    # ── Telemetry ──────────────────────────────────────────────────────────
    st.markdown('<p class="neo-section-title">Telemetry</p>', unsafe_allow_html=True)
    safe = (
        st.session_state.intl_log_text
        .replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    ) or "Ready. Select region, enter worksheet tab, and start scan."

    # Render terminal + inject JS to auto-scroll it to the bottom (not the page)
    terminal_html = (
        f'<div class="neo-terminal" id="skysync-terminal">{safe}</div>'
        "<script>"
        "(function(){"
        "  var el=document.getElementById('skysync-terminal');"
        "  if(el){ el.scrollTop=el.scrollHeight; }"
        "})();"
        "</script>"
    )
    st.markdown(terminal_html, unsafe_allow_html=True)

    # ── Live fare matrix ───────────────────────────────────────────────────
    st.markdown('<p class="neo-section-title">Live fare matrix</p>', unsafe_allow_html=True)
    rows = st.session_state.intl_fare_rows
    if rows:
        st.dataframe(
            rows,
            use_container_width=True,
            hide_index=True,
            column_config={
                "worker":   st.column_config.NumberColumn("W#",      width="small", format="%d"),
                "route":    st.column_config.TextColumn("Route",    width="small"),
                "airline":  st.column_config.TextColumn("Airline",  width="small"),
                "fare":     st.column_config.TextColumn("Fare Class"),
                "date":     st.column_config.TextColumn("Date",     width="small"),
                "price":    st.column_config.NumberColumn("Price",  format="%d"),
                "currency": st.column_config.TextColumn("Cur",      width="small"),
                "time":     st.column_config.TextColumn("Departure"),
            },
        )
    elif st.session_state.intl_scraping_started and not st.session_state.intl_scraping_done:
        st.markdown(
            '<div class="neo-banner-wait">◌ Parsing fares…</div>',
            unsafe_allow_html=True,
        )
    else:
        st.markdown(
            '<div class="neo-banner-wait">'
            'No data yet — configure and start scan.</div>',
            unsafe_allow_html=True,
        )

    # ── Completion banner ──────────────────────────────────────────────────
    if st.session_state.intl_scraping_done:
        st.markdown(
            '<div class="neo-banner-ok">✓ COMPLETE — GOOGLE SHEET UPDATED</div>',
            unsafe_allow_html=True,
        )
        pasted   = st.session_state.get("intl_pasted") or []
        unmapped = st.session_state.get("intl_unmapped") or []

        if pasted:
            st.markdown(
                '<p class="neo-section-title">Pasted to sheet</p>',
                unsafe_allow_html=True,
            )
            st.dataframe(pasted, use_container_width=True, hide_index=True)

        if unmapped:
            st.markdown(
                '<p class="neo-section-title">Not pasted — missing from CONFIG</p>',
                unsafe_allow_html=True,
            )
            st.dataframe(unmapped, use_container_width=True, hide_index=True)
            st.caption(
                "Add these rows to your CONFIG sheet "
                "(Route | Airline | Fare Name | Date Label | Fare Cell) "
                "and re-run to paste them."
            )


_live_panel()

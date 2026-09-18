"""Turn the Kaggle CSV into the per-second event bitmaps that Fig. 5 replays.

    curl -L -o /tmp/cosmetics.zip \
      "https://www.kaggle.com/api/v1/datasets/download/mkechinov/ecommerce-events-history-in-cosmetics-shop"
    unzip -d /tmp/cosmetics /tmp/cosmetics.zip        # five monthly CSVs

    python src/sim/extract.py 2019-Dec.csv.gz         # -> data/2019-Dec-3types.npz

The paper maps every event timestamp to a uniform 1-second slot and calls that the event's
actual occurrence time, so several events in the same second collapse to one slot. Its
real-world count of 1,654,771 is a slot count, not a row count: 2019-Dec with the
infrequent `purchase` type dropped has 1,647,519 occupied slots, the only candidate within
0.5 percent of it across all 341 month/type combinations. See README, Difference 6.

Only the bitmaps are kept -- one bit per second per event type -- so the ~100 MB CSV
becomes about 1 MB and Fig. 5 can be regenerated without the download.
"""
import calendar
import csv
import datetime
import gzip
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.abspath(os.path.join(HERE, "..", "..", "data"))
TYPES = ["view", "cart", "remove_from_cart"]        # `purchase` is the dropped infrequent one

MONTH = {m: i for i, m in enumerate(calendar.month_abbr) if m}   # "Dec" -> 12


def parse_month(name):
    """'2019-Dec.csv.gz' -> (year, month number)."""
    y, mon = os.path.basename(name).split(".")[0].split("-")
    return int(y), MONTH[mon[:3]]


def seconds_in(year, month):
    """Number of 1-second slots in that calendar month."""
    day1 = datetime.date(year, month, 1)
    nxt = datetime.date(year + (month == 12), month % 12 + 1, 1)
    return int((nxt - day1).total_seconds())


def extract(path, year, month):
    """Returns (bitmaps, rows, span): one packed-capable bitmap per retained type."""
    span = seconds_in(year, month)
    bits = {t: np.zeros(span, dtype=bool) for t in TYPES}
    rows = {t: 0 for t in TYPES}
    with gzip.open(path, "rt") as fh:
        r = csv.reader(fh)
        head = next(r)
        i_time, i_type = head.index("event_time"), head.index("event_type")
        for row in r:
            t = row[i_type]
            if t not in bits:
                continue
            ts = row[i_time]                                    # "2019-12-01 00:00:00 UTC"
            day = int(ts[8:10])
            sec = int(ts[11:13]) * 3600 + int(ts[14:16]) * 60 + int(ts[17:19])
            bits[t][(day - 1) * 86400 + sec] = True
            rows[t] += 1
    return bits, rows, span


if __name__ == "__main__":
    src = sys.argv[1] if len(sys.argv) > 1 else "2019-Dec.csv.gz"
    year, month = parse_month(src)
    label = f"{year}-{calendar.month_abbr[month]}"
    bits, rows, span = extract(src, year, month)
    os.makedirs(DATA, exist_ok=True)
    out = os.path.join(DATA, f"{label}-3types.npz")
    np.savez_compressed(out, **{t: np.packbits(bits[t]) for t in TYPES},
                        span=span, **{f"{t}_rows": rows[t] for t in TYPES})
    print(f"{label}: {span:,} second slots")
    for t in TYPES:
        print(f"  {t:18s} rows {rows[t]:>9,d}  occupied slots {int(bits[t].sum()):>9,d}")
    union = np.zeros(span, dtype=bool)
    for t in TYPES:
        union |= bits[t]
    print(f"  {'union of the three':18s}                    "
          f"occupied slots {int(union.sum()):>9,d}   <- paper says 1,654,771")
    print(f"\nwrote {out}  ({os.path.getsize(out) / 1e6:.1f} MB)")

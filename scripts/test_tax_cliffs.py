import csv
import io
import subprocess
import sys


result = subprocess.run([sys.argv[1]], check=True, capture_output=True, text=True)
rows = list(csv.DictReader(io.StringIO(result.stdout)))
expected = [
    (1320000, 3499),
    (3360000, 19999),
    (4890000, 9999),
    (6550000, 9999),
    (23500000, 39999),
    (24000000, 63999),
    (24500000, 63999),
    (25000000, 63999),
]
actual = [(int(row["income"]), int(row["net_loss"])) for row in rows]
if actual != expected:
    raise AssertionError(f"Unexpected exhaustive search results: {actual}")
print(
    "Tax cliff search: 25,000,001 adjacent pairs checked, 8 certified witnesses matched"
)

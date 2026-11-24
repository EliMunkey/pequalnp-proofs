"""Replay the shared nine-input exclusion and the pure ten-input exclusion."""
import argparse
from itertools import permutations
import os
from pathlib import Path
import subprocess
import tempfile


PACKAGE = Path(__file__).resolve().parent
BASE = PACKAGE.parent / "independent"
ORIGINAL_DELETION = {(0, 1), (1, 2), (2, 3), (0, 5), (1, 6), (2, 7),
                     (3, 8), (4, 6), (6, 8), (5, 8), (5, 7), (4, 7)}
SCALAR_EDGES = {(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5),
                (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (5, 8)}


def checked_pins():
    perm = next(p for p in permutations(range(9)) if all(
        tuple(sorted((p[i], p[j]))) in SCALAR_EDGES for i, j in ORIGINAL_DELETION))
    def relabel(x):
        return sum(((x >> i) & 1) << p for i, p in enumerate(perm))
    result = []
    for line in (BASE / "snapshot-deleted.txt").read_text().splitlines():
        mask, value, bound = map(int, line.split())
        mask, value = relabel(mask), relabel(value)
        if all((row & mask) != value for row in (42, 261)):
            result.append(f"{mask} {value} {bound}\n")
    if "".join(result) != (PACKAGE / "shared22.pins").read_text():
        raise ValueError("The supplied shared-row pin list differs from the reconstructed list")
    # Check that the remaining boundary forces exactly 510 of the 512 full-cube labels.
    truth = [any(((r >> a) & (r >> b) & 1) for a, b in SCALAR_EDGES) for r in range(512)]
    rows = [x for x in range(512) if all(bool((x >> i) & 1) != truth[x]
            or truth[x ^ (1 << i)] != truth[x] for i in range(9)) and x not in (42, 261)]
    def forced(x):
        return any(truth[r] == truth[x] and ((r & x) == (r if truth[x] else x)) for r in rows)
    if len(rows) != 22 or {x for x in range(512) if not forced(x)} != {42, 261}:
        raise ValueError("Shared boundary coverage failed")
    print(f"Checked {len(rows)} rows and {len(result)} restrictions", flush=True)


def run(work, name, source, args):
    binary = work / name
    subprocess.run([os.environ.get("CXX", "c++"), "-O3", "-std=c++17", str(source),
                    "-o", str(binary)], check=True)
    output = subprocess.check_output([str(binary), *map(str, args)], text=True)
    print(output, end="", flush=True)
    if "result=UNSAT" not in output:
        raise ValueError(f"Unexpected verdict from {name}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", choices=["check-inputs", "shared", "pure", "both"], default="both", nargs="?")
    args = parser.parse_args()
    checked_pins()
    with tempfile.TemporaryDirectory(prefix="petersen-positive-") as directory:
        work = Path(directory)
        if args.case in ("shared", "both"):
            run(work, "shared", PACKAGE / "shared22.cpp", [511, 15, -1, PACKAGE / "shared22.pins", 20, 1, 600000, 2])
        if args.case in ("pure", "both"):
            run(work, "pure", BASE / "physical.cpp", [1023, 18, -1, BASE / "snapshot-petersen.txt", 20, 1, 600000])


if __name__ == "__main__":
    main()

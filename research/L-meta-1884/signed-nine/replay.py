"""Replay the stronger nine-input signed exclusion from the research package."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "primary"))
import graph_bounds


def main():
    with tempfile.TemporaryDirectory(prefix="petersen-signed-nine-") as directory:
        work = Path(directory)
        binary = work / "search"
        graph_bounds.constraints("deleted", 4, ROOT / "evidence/small-costs.json", work)
        subprocess.run([os.environ.get("CXX", "c++"), "-O3", "-std=c++17",
                        str(ROOT / "signed-nine/search.cpp"), "-o", str(binary)], check=True)
        for budget, limit in ((14, 100000), (15, 900000)):
            command = [str(binary), str(budget), "deleted", "1", str(limit)]
            result = subprocess.run(command, cwd=work, text=True, stdout=subprocess.PIPE, check=True)
            print(result.stdout, end="", flush=True)
            if f"deleted gates {budget} sym 1 found 0 " not in result.stdout:
                raise RuntimeError("The expected exclusion did not reproduce.")


if __name__ == "__main__":
    main()

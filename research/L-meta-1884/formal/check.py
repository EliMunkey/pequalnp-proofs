"""Build the formal results from source in an empty temporary object directory."""
import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
BRIDGE = HERE.parent / "lean" / "PetersenPhysicalBoundary.lean"
REPORT = """import PetersenBound15
import PetersenFourteen
import PetersenPackedPin
import PetersenTwelve
import PetersenWitnessBounds
import PetersenPhysicalPin
import PetersenFiniteDSL
import PetersenFrontierSearch
import PetersenSingleton
import PetersenSmallPins
import PetersenBareBases
#print axioms PetersenBound15.public_lower
#print axioms PetersenFourteen.public_lower
#print axioms PetersenPackedPin.rejects_sound
#print axioms PetersenTwelve.public_lower
#print axioms PetersenBounds.twenty_works
#print axioms PetersenPhysicalPin.restrict_frontier
#print axioms PetersenFiniteDSL.L_meta_1884_of_finite_checks
#print axioms PetersenFrontier.L_meta_1884_of_frontier_exclusions
#print axioms PetersenSingleton.minimum_disjunction
#print axioms PetersenGraphCosts.mask119_lower
"""


def checked_modules(files):
    modules = {path.stem: path for path in files}
    done = set()
    order = []

    def visit(name, stack):
        if name in done:
            return
        if name in stack:
            raise ValueError(f"cyclic module dependency at {name}")
        text = modules[name].read_text()
        for dep in re.findall(r"^import (\S+)", text, re.M):
            if dep in modules:
                visit(dep, stack | {name})
            elif not dep.startswith(("Mathlib", "Std", "PEqualNP.")):
                raise ValueError(f"missing {dep}, required by {name}")
        if re.search(r"\b(sorry|admit|native_decide|axiom)\b", text):
            raise ValueError(f"unexpected placeholder, axiom or native evaluation in {name}")
        done.add(name)
        order.append(name)

    for name in sorted(modules):
        visit(name, set())
    return order


def run(project, bridge):
    project = project.resolve()
    def lake(*args):
        return subprocess.check_output(["lake", "env", *args], cwd=project, text=True).strip()
    lean = Path(lake("lean", "--print-prefix")) / "bin" / "lean"
    paths = [str((project / p).resolve()) for p in lake("printenv", "LEAN_PATH").split(os.pathsep) if p]
    sources = [bridge.resolve(), *HERE.rglob("*.lean")]
    with tempfile.TemporaryDirectory(prefix="petersen-lean-") as tmp:
        work = Path(tmp)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(work), *paths]))
        env.pop("LEAN_SYSROOT", None)
        for source in sources:
            shutil.copy2(source, work / source.name)
        (work / "Audit.lean").write_text(REPORT)
        order = checked_modules(list(work.glob("*.lean")))
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        print(lake("lean", "--version"), flush=True)
        for name in order:
            print(f"Checking {name}", flush=True)
            result = subprocess.run([str(lean), "-o", name+".olean", name+".lean"], cwd=work,
                                    env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            declared = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout)
            if result.returncode or any(set(re.findall(r"[\w.]+", ax)) - allowed for ax in declared):
                print(result.stdout, flush=True)
                raise SystemExit(result.returncode or 1)
            for line in re.findall(r"'[^']+' depends on axioms:\s*\[[^\]]*\]", result.stdout):
                print(" ".join(line.split()), flush=True)
            if name == "Audit" and len(declared) != REPORT.count("#print axioms"):
                raise SystemExit("Incomplete axiom report.")
        print(f"Checked {len(order)-1} source modules and the axiom report.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="lean directory of the built, pinned proof repository")
    parser.add_argument("--bridge", type=Path, default=BRIDGE)
    args = parser.parse_args()
    run(args.project, args.bridge)

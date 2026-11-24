"""Build the formal results from source in an empty temporary object directory."""
import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

HERE = Path(__file__).resolve().parent
BRIDGE = HERE.parent / "lean" / "PetersenPhysicalBoundary.lean"
REPORT = """import PetersenSixRoots
import PetersenBound17
import PetersenNineLift
import PetersenElevenCensus
import PetersenBound16
import PetersenBound15
import PetersenPackedRoot
import PetersenPhysicalOrbit
import PetersenPhysicalProjection
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
#print axioms PetersenSixRoots.original
#print axioms PetersenBound17.public_lower
#print axioms PetersenNineLift.signed
#print axioms PetersenElevenCensus.close
#print axioms PetersenBound16.public_lower
#print axioms PetersenPackedRoot.original_of_word_exclusions
#print axioms PetersenPhysicalOrbit.no_physical
#print axioms PetersenPhysicalProjection.blocks
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


def module_name(path):
    certificates = HERE / "certificates"
    if path.is_relative_to(certificates):
        return ".".join(path.relative_to(certificates).with_suffix("").parts)
    return path.stem

def checked_modules(modules):
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


def run(project, bridge, jobs):
    project = project.resolve()
    def lake(*args):
        return subprocess.check_output(["lake", "env", *args], cwd=project, text=True).strip()
    lean = Path(lake("lean", "--print-prefix")) / "bin" / "lean"
    paths = [str((project / p).resolve()) for p in lake("printenv", "LEAN_PATH").split(os.pathsep) if p]
    sources = [bridge.resolve(), *HERE.rglob("*.lean")]
    if len({module_name(p) for p in sources}) != len(sources):
        raise ValueError("Duplicate Lean module name in the package.")
    with tempfile.TemporaryDirectory(prefix="petersen-lean-") as tmp:
        work = Path(tmp)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(work), *paths]))
        env.pop("LEAN_SYSROOT", None)
        modules = {}
        for source in sources:
            name = module_name(source)
            destination = work / Path(*name.split(".")).with_suffix(".lean")
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
            modules[name] = destination
        modules["Audit"] = work / "Audit.lean"
        modules["Audit"].write_text(REPORT)
        order = checked_modules(modules)
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        print(lake("lean", "--version"), flush=True)
        def build(name):
            logs = [f"Checked {name}"]
            relative = modules[name].relative_to(work)
            result = subprocess.run([str(lean), "-j", "2", "-o", str(relative.with_suffix(".olean")), str(relative)], cwd=work,
                                    env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            declared = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout)
            if result.returncode or any(set(re.findall(r"[\w.]+", ax)) - allowed for ax in declared):
                print(result.stdout, flush=True)
                raise SystemExit(result.returncode or 1)
            for line in re.findall(r"'[^']+' depends on axioms:\s*\[[^\]]*\]", result.stdout):
                logs.append(" ".join(line.split()))
            if name == "Audit" and len(declared) != REPORT.count("#print axioms"):
                raise SystemExit("Incomplete axiom report.")
            return logs
        names = set(order)
        pending = {name: set(re.findall(r"^import (\S+)", modules[name].read_text(), re.M)) & names for name in order}
        done = set()
        running = {}
        with ThreadPoolExecutor(max_workers=jobs) as workers:
            while pending or running:
                for name in list(pending):
                    if len(running) == jobs:
                        break
                    if pending[name] <= done:
                        running[workers.submit(build, name)] = name
                        del pending[name]
                if not running:
                    raise ValueError("Compiler dependency cycle.")
                finished, _ = wait(running, return_when=FIRST_COMPLETED)
                for task in finished:
                    name = running.pop(task)
                    print("\n".join(task.result()), flush=True)
                    done.add(name)
        print(f"Checked {len(order)-1} source modules and the axiom report.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="lean directory of the built, pinned proof repository")
    parser.add_argument("--bridge", type=Path, default=BRIDGE)
    parser.add_argument("--jobs", type=int, default=2, choices=range(1,17), metavar="N", help="parallel compiler jobs (1–16, default 2)")
    args = parser.parse_args()
    run(args.project, args.bridge, args.jobs)

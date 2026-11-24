"""Replay the two exclusions using Python 3.10+ and a C++17 compiler."""
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "primary"
sys.dont_write_bytecode = True
sys.path.insert(0, str(SRC))
import graph_bounds


def control():
    literal = r'x7 \((\d+) : Fin \(10 : ℕ\)\)'
    edges = [(int(a), int(b)) for a, b in re.findall(literal + ' && ' + literal, (ROOT / 'statement.txt').read_text())]
    assert edges == graph_bounds.edges and len(edges) == 15
    net = json.loads((SRC / 'known-20.json').read_text())
    assert len(net) == 20
    positives = 0
    for row in range(1024):
        bits = [bool(row & (1 << i)) for i in range(10)]
        wires = bits + [not bits[0], False, True]
        for op, i, j in net:
            assert 0 <= i < len(wires) and 0 <= j < len(wires)
            assert op in ('and', 'or')
            wires.append(wires[i] and wires[j] if op == 'and' else wires[i] or wires[j])
        expected = any(bits[i] and bits[j] for i, j in edges)
        assert wires[-1] == expected
        positives += expected
    assert positives == 948
    print('20-gate control matches the posted expression on 1,024 rows.', flush=True)


def run(work):
    work.mkdir(parents=True, exist_ok=True)
    bins = {}
    for name in ('frontier', 'pinned', 'ordered'):
        bins[name] = work / name
        subprocess.run([os.environ.get('CXX', 'c++'), '-O3', '-std=c++17', str(SRC / (name + '.cpp')),
                        '-o', str(bins[name])], check=True)

    def verdict(binary, budget, mode, expected, *extra, cwd=work):
        args = [str(bins[binary]), str(budget), mode, *map(str, extra)]
        result = subprocess.run(args, cwd=cwd, check=True, stdout=subprocess.PIPE, text=True)
        first = result.stdout.splitlines()[0]
        print(first, flush=True)
        assert f'found {int(expected)} ' in first, args

    # Raw exhaustive checks on graphs through seven essential vertices.
    costs = work / 'small-costs.json'
    graph_bounds.costs(bins['frontier'], costs)
    recorded = json.loads((ROOT / 'evidence/small-costs.json').read_text())
    assert {k: v['cost'] for k, v in json.loads(costs.read_text()).items()} == {k: v['cost'] for k, v in recorded.items()}

    # Each stage uses only smaller graphs already checked. The tests at sizes
    # 11 and 12 for the nonedge type bracket its exact complexity.
    for mode in ('delmask3', 'delmask5'):
        graph_bounds.constraints(mode, 3, costs, work)
    verdict('pinned', 12, 'delmask3', False, 0)
    verdict('frontier', 11, 'delmask5', False, 0)
    verdict('pinned', 12, 'delmask5', True, 0)
    graph_bounds.constraints('deleted', 4, costs, work)
    verdict('pinned', 14, 'deleted', False, 0)
    graph_bounds.constraints('petersen', 4, costs, work)
    verdict('pinned', 17, 'petersen', False, 1)

    # In the remaining branch all gates are physical AND/OR. Deleting
    # vertex 0 leaves two orbits for the distinguished complemented input.
    for pivot in (0, 1):
        verdict('ordered', 15, 'deleted', False, 1, -1, pivot)
    physical = work / 'physical'
    physical.mkdir(exist_ok=True)
    pins = []
    upgraded = 0
    for line in (work / 'pins-petersen.txt').read_text().splitlines():
        mask, value, lower = map(int, line.split())
        if mask.bit_count() == 1 and value == 0:
            assert lower == 15
            lower = 16
            upgraded += 1
        pins.append(f'{mask} {value} {lower}\n')
    assert upgraded == 10
    (physical / 'pins-petersen.txt').write_text(''.join(pins))
    verdict('ordered', 18, 'petersen', False, 1, cwd=physical)
    print('Both exclusions reproduced.', flush=True)


if __name__ == '__main__':
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument('--work-dir', type=Path, help='Keep binaries, generated constraints and intermediate evidence here.')
    args.add_argument('--control-only', action='store_true')
    options = args.parse_args()
    control()
    if not options.control_only:
        if options.work_dir:
            run(options.work_dir.resolve())
        else:
            with tempfile.TemporaryDirectory(prefix='petersen-1884-') as t:
                run(Path(t))

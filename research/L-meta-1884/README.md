# Excluding 18 gates for the Petersen edge function

An exhaustive computer-assisted proof rules out every circuit in [L-meta-1884](https://github.com/open-goat/pequalnp-proofs/pull/8799) with **18 or fewer gates**. The minimum in the stated model is therefore **19 or 20**. The known 20-gate construction passes all 1,024 inputs.

The exact public proposition is in [statement.txt](statement.txt). The target is true when the selected Petersen vertices contain an edge. Legal circuits can reuse wires. AND and OR have at most two inputs, and NOT reads its first input. The problem also permits arbitrary input rewiring and a free unary function of vertex zero.

## Evidence

| Case | Computational conclusion |
| --- | --- |
| Every wire and its complement are available for free | No circuit with at most 17 binary gates. The primary search visited 1,175,872 states. [Log](evidence/signed-17.log) |
| All 18 gates are AND or OR, with both signs of vertex zero available | No circuit with 18 gates. The primary search visited 25,582,855 states. [Log](evidence/and-or-18.log) |

A second implementation independently excluded both cases. It visited 1,176,021 states for the 17-gate search and 32,942,413 states for the 18-gate search. [Independent signed results](independent/replay-all.log) · [Independent physical results](independent/physical-all.log)

The first search counts binary gates only. A legal circuit that pays for a NOT, a degenerate gate or an unused gate has at most 17 effective binary gates and falls under the first exclusion. The second search covers the only remaining case. A Lean proof establishes this implication for the project's actual evaluator, including its handling of missing wires, duplicated inputs and arbitrary output indices. [Lean bridge](lean/PetersenPhysicalBoundary.lean)

Lean independently proves that every circuit for the original problem needs at least **17 gates**, and checks the 20-gate witness directly in the posted evaluator. The [formal proof and replay instructions](formal/README.md) give both theorem names. Lean also verifies the bridge, the 38-row compression and auxiliary accounting lemmas. The two exhaustive searches through 18 gates run as ordinary programs. The full statement does not currently have an assumption-free Lean proof in this package. The existing public pull request contains the earlier reduction and has its own checker status.

The signed nine-input subproblem gives a separate way to measure the remaining gap. Lean excludes all circuits through 14 signed binary gates on each of the ten vertex deletions. A stronger exhaustive search excludes 15 signed gates on 512 rows. The released program reproduced that result from scratch after visiting 32,045,906 states. [Nine-input Lean proof](formal-nine/README.md) · [Stronger exhaustive replay](signed-nine/README.md)

Lean also proves the exact signed minimum for 59,038 restrictions of the ten-input problem. For the ten single-vertex deletions, a checked 16-gate witness matches the stronger exhaustive exclusion. These results give exact minima for all proper restrictions when the computational and Lean results are combined. [Restriction catalogue and witness](cofactors/README.md)

A further Lean theorem reduces an 18-gate lower bound for the posted evaluator to 18 explicit first-gate questions on seven or eight inputs. The ten-input search now has a checked proof of that implication. [Remaining obligations and reproducible Lean sources](first-gates/README.md)

## Replay

The primary replay requires Python 3.10 or later and a C++17 compiler. It uses a temporary directory for compiled binaries and generated tables. From this directory run

```sh
python3 reproduce.py
```

For a quick check of the 20-gate construction on all 1,024 rows, use `python3 reproduce.py --control-only`. To retain intermediate files, pass `--work-dir /path/to/new-directory`. To replay the second implementation, run `python3 independent/independent.py --all`. [Independent replay instructions](independent/README.md) · [Mathematical argument](ARGUMENT.md)

The Lean sources were checked against [proof-repository revision 074709b](https://github.com/open-goat/pequalnp-proofs/tree/074709bd01fc526b9f6279e5b0a028946ceb39fb), using Lean 4.36.0. With that checkout built, run `lake env lean /absolute/path/to/lean/PetersenPhysicalBoundary.lean` from its lean directory. The final theorem takes the two finite exclusions as hypotheses.

The packaged replay was also tested against circuits with known answers. A separate direct enumerator agreed with the physical search on 522 small instances, including 186 positive instances. Two audits cover the scheduling, pin accounting and treatment of the free input. [Fixture results](evidence/ordered-pin-fixture.json) · [Search audit](evidence/primary-audit.md) · [Second audit](evidence/second-audit.md)

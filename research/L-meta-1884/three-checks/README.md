# Three finite checks for the original theorem

Lean proves that the exact L-meta-1884 statement follows from the three exclusions below. The conclusion uses the posted circuit evaluator, arbitrary input rewiring, the free unary function of vertex zero and the 18-gate budget. [Formal statement](PetersenThreeChecks.lean) · [Kernel axiom reports](axioms.log)

| Circuit model | Inputs tested | Exclusion needed |
| --- | ---: | --- |
| Ten inputs with freely complemented wires | 1,024 | No circuit through 17 binary gates |
| Ten inputs using AND and OR | 30 | No circuit through 18 gates |
| Nine inputs using AND and OR | 22 | No circuit through 15 gates |

The signed exclusion has a kernel-checked reduction to 18 explicit first-gate questions on seven or eight inputs. A follow-up certificate settles the seven-input question with gate type (0, 2, 1), the signal formed by the first input AND the complement of the third. [First-gate statements and sources](../first-gates/README.md) · [Seven-input proof](theta-first-0-2-1.tar.gz)

For the positive ten-input case, the 30 tests are the minimal positive and maximal negative assignments of the Petersen edge predicate. For the marked-input case, the proof analyzes the readers of both signs. It reduces their behavior to three nine-input functions. On 24 boundary assignments these functions and their symmetry image differ only at the two independent triples encoded by 42 and 261. Dropping those two assignments gives a single 22-row problem. Lean proves that a lower bound on these 22 rows is equivalent, at every gate budget, to the four corresponding 24-row lower bounds. [Equivalence proof](PetersenShared22.lean)

The 22-row search excludes 15 gates after 1,303,435 states. Its 1,435 pin bounds come from restrictions that exclude both omitted triples. The replay reconstructs these bounds and checks that monotonicity fixes 510 of the 512 full-cube labels. All three exclusions have independent computational support from the research package. The unconditional Lean lower bound on the posted evaluator is still 17. [22-row search output](shared22-search.log) · [Full computational evidence](../README.md)

## Replay the Lean implication

With the pinned upstream Lean project already built, run this from the extracted research package. The second argument must be a new working directory. The script verifies the manifests in both archives, combines their source trees and checks the entry module `PetersenThreeChecks`. The combined tree contains 1,699 local Lean modules. The optional `--prepare-only` verifies and extracts the source tree.

```sh
python3 three-checks/replay.py /path/to/pequalnp-proofs/lean /path/to/new/work --jobs 2
```

To replay just the extra seven-input first-gate proof, extract the theta archive and follow the README inside it. [Additional Lean sources](additional-lean.tar.gz) · [Ten-input source archive](../first-gates/ten-input.tar.gz)

## Replay the positive searches

A C++17 compiler and Python 3.10 or later suffice for the numeric replay. `shared` evaluates the 22-row exclusion, `pure` evaluates the 30-row exclusion, and `both` runs both. The larger searches can take several minutes.

```sh
python3 three-checks/numeric.py check-inputs
python3 three-checks/numeric.py both
```

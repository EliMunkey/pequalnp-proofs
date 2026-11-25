# Six remaining signed cases

The original question asks whether any circuit with 18 or fewer gates realizes the Petersen graph edge detector, with arbitrary input rewiring and an extra unary input. Two exhaustive programs exclude every such circuit. The unconditional lower bound for the original circuit that we have checked in Lean is 17. The [18-gate computations](../README.md) and [three finite subproblems](../three-checks/README.md) give the context for this checkpoint.

## What Lean checks

- The signed subproblem now follows from six explicit eight-input exclusions. All eight previously outstanding seven-input representatives are proved, together with four of the ten eight-input cases. Graph symmetries extend those eight proofs to all 23 labeled starts in their orbits. The complete statement still needs the six listed eight-input exclusions and both positive-circuit exclusions. The exact implication and all six hypotheses are in [PetersenReducedStarts.lean](PetersenReducedStarts.lean).
- The common 22-assignment problem on nine ordinary inputs requires at least 14 AND/OR gates. The full submission needs at least 16. All finite steps for the bound of 14 have been checked by the kernel.
- On that same nine-input problem, fixing one input gives four kinds of restriction up to symmetry. Three costs are now exact in Lean. Setting input 0 to zero costs 12 gates, setting it to one costs 8, and setting input 4 to one costs 10. For input 4 set to zero, the archive contains a checked 13-gate construction. Inputs are numbered from zero in the nine-input labeling. The lower bounds here concern ordinary circuits on the indicated partial truth tables. Lean checks that the boundary tests give the same answer as testing every required assignment out of 256 for each restriction. [Entry module](PetersenRemainingCases.lean) · [Kernel axiom reports](axioms.log)

Two general lemmas used in these proofs may help with related searches. For an ordinary AND/OR circuit, a gate can be replaced by a gate on the available wires that agrees with the target on a larger set of rows. Lean proves that choosing such maximal gates preserves a minimum-size solution. A second lemma bounds the cost of a suffix by simulating each live signal on a smaller truth table. It can charge one gate for a simulated signal and recover a gate when a live signal is forced to a constant.

## Reproduce

The archive includes all 3,432 local Lean source modules used by the entry point, the module inventory, a replay script, and source checksums. Use Lean 4.36.0 and the project dependencies at revision `074709bd01fc526b9f6279e5b0a028946ceb39fb`. Run these commands in this directory, with `PROOFS` set to the path of that upstream checkout.

```sh
tar -xzf sources.tar.gz
cd petersen-remaining
shasum -a 256 -c SHA256SUMS
python3 replay.py "$PROOFS/lean" --jobs 2
```

The compressed archive has SHA-256 `f771be2d113b24ff20eb1f5294f084e8909f1e29ea4265d5edfdc51021e4f928`. A full replay rebuilds a substantial collection of smaller graph lemmas before reaching the entry point.

This revision also corrects the choice of the shared `Extra191` module in this bundle, the nine-input bundle, and three first-gate bundles. Their source now includes the `b51_0` lemma used by `D10Basis`. The corrected helper and its dependent module passed an isolated Lean replay.

# Kernel-checked bounds for L-meta-1884

Lean proves that **every circuit computing the posted ten-input function needs at least 17 gates**. It also verifies a **20-gate circuit** on all 1,024 inputs in the posted evaluator. The stronger lower bound of 19 comes from the two exhaustive programs in the [research package](../README.md). Closing L-meta-1884 in the swarm requires a Lean proof that excludes all circuits through 18 gates.

The lower-bound theorem is `PetersenBound17.public_lower`. It covers arbitrary input rewiring and the extra unary function of vertex zero. The proof excludes all circuits through 12 signed binary gates on the eight-vertex graph obtained by deleting the endpoints of an edge. For the full graph it checks both possible first-pair types and transfers each remaining branch to a certified smaller graph. The witness theorem is `PetersenBounds.twenty_works`. [Axiom report for the bound and the reductions](../evidence/formal-17.log)

## Replay

Use Lean 4.36.0 and a built copy of the [pinned proof repository](https://github.com/open-goat/pequalnp-proofs/tree/074709bd01fc526b9f6279e5b0a028946ceb39fb). From this directory run

```sh
python3 check.py /absolute/path/to/pequalnp-proofs/lean
```

The script builds every included module from source in an empty temporary object directory. It checks theorem dependencies against the three standard axioms used here, `propext`, `Classical.choice` and `Quot.sound`. The seven-vertex proof is split into small source modules so the kernel can check the finite cases separately. The argument, its numerical certificates and the circuit witness are all included.

The [15-gate checkpoint](../evidence/formal-15.log) records a clean run of 68 source modules. Its seven-vertex exclusion reaches nine gates. The 16-gate result adds a complete ten-gate exclusion using four graph symmetries, 250 branching states and 2,857 terminal restriction certificates. The [clean 16-gate replay](../evidence/formal-16-clean.log) compiled all 227 source modules from an empty object directory and checked the final axiom report. The [short theorem report](../evidence/formal-16.log) records the transitive axioms for the seven-vertex exclusion and its transfer to the posted evaluator.

For the full 18-gate exclusion, `PetersenSixRoots.original` proves the posted statement from seven explicit hypotheses. One excludes 15 signed binary gates on the nine-vertex graph obtained by deleting one vertex. The other six exclude 17 further AND/OR gates after a particular first OR. These suffix problems each allow constants and both signs of the distinguished input. The proof uses row maps that Lean checks separately for each family. The exhaustive programs rule out all original circuits through 18. Closing the swarm problem still requires checking the remaining finite exclusions in Lean.

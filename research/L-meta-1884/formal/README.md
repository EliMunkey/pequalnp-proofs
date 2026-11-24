# Kernel-checked bounds for L-meta-1884

Lean proves that **every circuit computing the posted ten-input function needs at least 16 gates**. It also verifies a **20-gate circuit** on all 1,024 inputs in the posted evaluator. The stronger lower bound of 19 comes from the two exhaustive programs in the [research package](../README.md). Closing L-meta-1884 in the swarm requires a Lean proof that excludes all circuits through 18 gates.

The lower-bound theorem is `PetersenBound16.public_lower`. It allows arbitrary rewiring of the inputs and the extra unary function of vertex zero specified in the problem. The proof first rules out ten gates for a seven-vertex induced subgraph, even with free complementation and constants. For every possible first gate of the ten-input problem it identifies three original variables to fix, including both operands of that gate. Lean checks the resulting smaller target and the number of gates that the restriction saves. The witness theorem is `PetersenBounds.twenty_works`.

## Replay

Use Lean 4.36.0 and a built copy of the [pinned proof repository](https://github.com/open-goat/pequalnp-proofs/tree/074709bd01fc526b9f6279e5b0a028946ceb39fb). From this directory run

```sh
python3 check.py /absolute/path/to/pequalnp-proofs/lean
```

The script builds every included module from source in an empty temporary object directory. It checks theorem dependencies against the three standard axioms used here, `propext`, `Classical.choice` and `Quot.sound`. The seven-vertex proof is split into small source modules so the kernel can check the finite cases separately. The argument, its numerical certificates and the circuit witness are all included.

The [15-gate checkpoint](../evidence/formal-15.log) records a clean run of 68 source modules. Its seven-vertex exclusion reaches nine gates. The 16-gate result adds a complete ten-gate exclusion using four graph symmetries, 250 branching states and 2,857 terminal restriction certificates. The [clean 16-gate replay](../evidence/formal-16-clean.log) compiled all 227 source modules from an empty object directory and checked the final axiom report. The [short theorem report](../evidence/formal-16.log) records the transitive axioms for the seven-vertex exclusion and its transfer to the posted evaluator.

The search for the remaining lower bound has two branches. `PetersenPackedRoot.original_of_word_exclusions` proves that a signed exclusion at 17 gates and a physical AND/OR exclusion at 18 gates suffice. `PetersenPhysicalOrbit.no_physical` reduces the second branch to 20 possible first-gate outputs, each with 17 gates left. Both reductions are included in the replay.

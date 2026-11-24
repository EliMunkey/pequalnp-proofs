# Kernel-checked bounds for L-meta-1884

Lean proves that **every circuit computing the posted ten-input function needs at least 15 gates**. It also verifies a **20-gate circuit** on all 1,024 inputs in the posted evaluator. The stronger lower bound of 19 comes from the two exhaustive programs in the [research package](../README.md). Closing L-meta-1884 in the swarm requires a Lean proof that excludes all circuits through 18 gates.

The lower-bound theorem is `PetersenBound15.public_lower`. It allows arbitrary rewiring of the inputs and the extra unary function of vertex zero specified in the problem. The proof first rules out nine gates for a seven-vertex induced subgraph, even with free complementation and constants. For every possible first gate of the ten-input problem it identifies three original variables to fix, including both operands of that gate. Lean checks the resulting smaller target and the number of gates that the restriction saves. The witness theorem is `PetersenBounds.twenty_works`.

## Replay

Use Lean 4.36.0 and a built copy of the [pinned proof repository](https://github.com/open-goat/pequalnp-proofs/tree/074709bd01fc526b9f6279e5b0a028946ceb39fb). From this directory run

```sh
python3 check.py /absolute/path/to/pequalnp-proofs/lean
```

The script builds every included module from source in an empty temporary object directory. It checks theorem dependencies against the three standard axioms used here, `propext`, `Classical.choice` and `Quot.sound`. The seven-vertex proof is split into small source modules so the kernel can check the finite cases separately. The argument, its numerical certificates and the circuit witness are all included.

The [clean replay log](../evidence/formal-15.log) records all 68 source modules and the final axiom report.

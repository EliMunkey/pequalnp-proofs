# Signed nine-vertex exclusion

Delete vertex zero from the posted graph and retain all 512 assignments to the nine surviving vertices. A signed circuit can invert any input or gate output for free. The program finds no such circuit with 15 binary gates. Its 14-gate control visits 15,797 states and its 15-gate search visits 32,045,906 states. [Original results](results.log) · [Replay of the packaged source](packaged-replay.log)

From the research package root, run

```sh
python3 signed-nine/replay.py
```

The script rebuilds its C++17 executable in a temporary directory and generates all 1,938 smaller restriction bounds from the same inputs used by the primary search. Each published state count includes the root. For a fixed restriction, the extra pruning rule reconstructs only the union of the ancestor gates needed by the surviving restricted signals. Surviving constant signals must still be consumed in the last-use schedule. When the budget falls below the verified cost of the smaller target, the branch closes. Automorphisms of the nine-vertex graph identify equivalent first pairs.

The original ten-input problem and its independently replayed 18-gate exclusion are documented in the [research overview](../README.md). The 15-gate nine-input result here uses ordinary exhaustive computation.

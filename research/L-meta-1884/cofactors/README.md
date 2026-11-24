# What happens when inputs are fixed

For 59,038 of the 59,049 ways to leave each Petersen vertex free or fix it to zero or one, Lean proves the exact number of signed binary gates. A signed circuit can reuse signals and invert any wire for free. The proof covers every restriction with two or more fixed inputs and all ten ways to fix a single vertex to one. Each single-true case needs exactly 11 gates.

| Two fixed vertices | Both zero | One zero, one one | Both one |
| --- | ---: | ---: | ---: |
| Adjacent | 13 | 10 | 0 |
| Nonadjacent | 12 | 8 | 7 |

The other ten proper restrictions fix one vertex to zero. For each, Lean proves a lower bound of 15 and checks a 16-gate upper bound. The separate exhaustive search rules out 15 signed gates. Taken together, these results determine the signed minimum for every proper restriction. The full ten-vertex instance is the remaining entry. [Nine-vertex lower-bound proof](../formal-nine/README.md) · [Exhaustive search at 15](../signed-nine/README.md)

The witness uses only ordinary binary AND and OR. In the JSON file the original vertices 1 through 9 become input wires 0 through 8, and gate outputs receive consecutive wire numbers starting at 9. Output wire 24 agrees with the edge predicate on all 512 assignments. Lean transports the upper bound to all ten vertex deletions. [Witness gates](nine-upper.json) · [Lean axiom report](axioms.log)

## Replaying the proofs

From a directory containing the archive, with Lean 4.36.0 and the pinned project's dependencies built, run

```sh
tar -xzf sources.tar.gz
python3 petersen-cofactors/replay.py /absolute/path/to/pequalnp-proofs/lean --jobs 4
```

The archive contains 466 Lean source modules, a file manifest and the replay script. The entry module is `CofactorCheckpoint`. The main theorems are `PetersenMaskCofactor.except_one_zero_and_full`, `PetersenMaskCofactor.unconditional_pair` and `PetersenDeletionUpper.all`. The compressed archive SHA-256 is `66b6a1021772889441e729d5f95d047914cd597880c6fde627810d41d02b4128`. [Download the archive](sources.tar.gz) · [Pinned upstream source](https://github.com/open-goat/pequalnp-proofs/tree/074709bd01fc526b9f6279e5b0a028946ceb39fb)

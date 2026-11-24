# Which first gates can help?

Lean checks that 18 explicit smaller lower bounds imply that every circuit computing the posted ten-input Petersen function has at least 18 gates. Eight obligations have seven inputs. Ten have eight inputs. Each supplies one specified binary gate output for free and asks whether it can save a gate. The theorem applies to the original evaluator with arbitrary input rewiring and the free unary function. [Exact obligations and theorem](Full18EighteenStarts.lean)

The proof first allows every complement for free. Up to graph symmetry, a 17-gate solution in this stronger model must start by OR-ing two adjacent vertices or two nonadjacent vertices. A certificate follows both starts and uses previously checked graph restrictions. After symmetry, the kernel replay used 113 expanding representatives and 279 transfers between states. No lower bound for a full nine-vertex deletion beyond the published signed lower bound of 15 is assumed. [Two possible starts](Full18TwoStarts.lean) · [Certificate composition](Full18SymConditional.lean)

Two other source archives give unconditional first-gate results. For 15 smaller induced graphs, Lean checks 227 forbidden first-gate types up to symmetry and transports the results to 606 individually labeled gates. For the two eight-vertex graphs, it separately checks eight supplied gate types on the adjacent-deletion graph and ten on the nonadjacent-deletion graph. In each case the supplied gate leaves the circuit cost at the original minimum. [Kernel axiom reports](axioms.log)

Lean also verifies optimal continuations for the other 70 gates on the 15 smaller graphs. That gives a yes-or-no answer for every one of the 676 labeled, distinct-input first gates in the signed model. On the five-cycle an optimal circuit can begin with an AND of neighbors or an OR of vertices at distance two. On the six-cycle the only optimal first gates are the six ORs of distance-two pairs. [Complete classification and witness programs](optimal-first-gates.tar.gz) · [Axiom reports](optimal-axioms.log)

The 18 assumptions in the ten-input theorem still require individual proofs. The unconditional Lean lower bound for the original evaluator is 17 gates. Two independent exhaustive programs establish the stronger lower bound of 19. [Formal lower bound](../formal/README.md) · [Full computational result](../README.md)

## Replay from source

The archives contain Lean source and independent entry points. With the upstream project's dependencies built at revision `074709bd01fc526b9f6279e5b0a028946ceb39fb` and Lean 4.36.0 active, run the corresponding commands from a fresh directory. The ten-input archive contains 1,667 project-specific modules and keeps all 18 outstanding lower bounds explicit in its theorem statement. [Pinned upstream sources](https://github.com/open-goat/pequalnp-proofs/tree/074709bd01fc526b9f6279e5b0a028946ceb39fb)

```sh
tar -xzf ten-input.tar.gz
python3 petersen-starts/replay.py /path/to/pequalnp-proofs/lean --jobs 2

tar -xzf fifteen-minors.tar.gz
python3 petersen-fifteen-first-starts/replay.py --project /path/to/pequalnp-proofs/lean --jobs 2

tar -xzf optimal-first-gates.tar.gz
python3 petersen-exact-first-starts/replay.py --project /path/to/pequalnp-proofs/lean --jobs 2

tar -xzf eight-input.tar.gz
python3 first-eight-starts/replay.py /path/to/pequalnp-proofs/lean --jobs 2
```

[Ten-input certificate](ten-input.tar.gz) · [Fifteen smaller graphs](fifteen-minors.tar.gz) · [Eight-input first-gate results](eight-input.tar.gz)

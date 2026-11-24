# Why the enumerations cover the circuit model

## First exclusion

Remove gates outside the output cone. Allow every wire to be complemented at zero cost, and represent a binary gate as the conjunction of two signed wires, with either output sign available. This basis contains every AND and OR and permits bypassing constants, unary operations, repeated signals and NOT gates. Each input to a first gate can have either sign. An exact circuit in this model must depend on all ten vertices. For each vertex, fixing a neighbor to true and every other vertex to false makes that vertex control the answer.

A search state records the live Boolean signals. A signal stays live until its last use. At a gate the search tries every distinct pair, every permitted operation, and every choice of which operands are retired. A binary gate that keeps both operands spends two additional wire uses. Keeping one spends one, and retiring both spends none. Starting with n essentials and ending with one output, a circuit of g binary gates spends exactly g−n+1 additional uses. Conversely, at k live wires with c additional uses left, at most k−1+c gates remain. This counts reuse at any depth.

Oppositely labelled input assignments must remain distinguishable by the live wires. When one operand is retired, a pair that differed only at that operand must still be separated by the new gate. When both are retired, pairs that differed at both operands also have to stay distinguishable. The signed search checks those cases on the full truth table. With free inversion we store one representative of each pair of complementary functions. An optimal circuit has no gate that merely reconstructs a constant or an available signed wire.

## Restrictions and saved gates

For a pinning of selected vertices, some live signals become constant. Each constant must be read before reaching a nonconstant output. A gate that reads a constant simplifies to a constant or a signed wire, and can be removed. Reading two constants produces a constant, so a single simplified gate can reduce the number of live constants by at most one. With d known constant wires at a state, at least d gates in the continuation can be removed. This argument uses the actual last-use schedule. A nonconstant-output condition is required and is checked when generating the pin constraints.

A partial circuit supplies an upper bound on the cost of its restricted live wires. Simplify every gate with a constant operand. A stronger bound counts only the surviving ancestors needed for the current frontier. Each input or known constant has an empty ancestor set. A bypassed gate inherits its surviving parent's set. An unresolved binary gate takes the union of its parents' sets and adds itself. Sharing gates is permitted, so the size of the union across all live signals bounds the cost of producing all of them at once. If that cost plus k−1+c−d is smaller than a previously proved lower bound for the restricted target, the prefix cannot extend to an exact circuit.

An input restricted to zero removes its vertex and incident edges. Restricting it to one makes its neighbors singleton OR terms, unless an edge is already forced. The remaining function is the OR of independent singleton variables and an induced graph's edge predicate. For a nonconstant residual graph function, adjoining one separate singleton increases the binary cost by exactly one. OR supplies the upper bound. Setting the singleton to zero removes its first effective reader, leaving a circuit for the residual graph. A pure disjunction of t essentials costs t−1.

The dependency order prevents circular bounds.

1. Exhaustively enumerate the induced graph types through seven essential vertices. Classify them by complete adjacency codes minimized under consistent vertex relabellings. The constructive upper bound groups edges into stars at a vertex cover, then ORs the stars.
2. Exclude 12 gates for the eight-vertex graph obtained by deleting an adjacent pair. For a deleted nonadjacent pair exclude 11 gates and exhibit a circuit at 12. Only smaller induced graphs enter these searches.
3. Exclude 14 gates for the nine-vertex graph obtained by deleting one vertex. Both eight-vertex bounds are now available.
4. Exclude 17 binary gates for the full Petersen graph. The primary search uses 3,040 pin constraints. Every pair of distinct vertices is an edge or a nonedge, and Petersen automorphisms act transitively on each class. All four choices of first-gate signs are tested for both representatives.

## Final AND/OR exclusion

If a circuit with at most 18 total gates computes the target, the first exclusion requires all 18 to be effective binary gates. The remaining model has AND/OR at every gate. It grants all ten positive inputs and also the complement of vertex zero. This includes the posted rewiring and unary choices. Supplying both polarities together costs nothing and the search allows either polarity at every read.

Once vertex zero is fixed, every signal and the target are monotone in the other nine inputs. It suffices to compute the truth table on the minimal positive and maximal negative assignments within each of the two slices. There are **38 distinct boundary assignments**. Every positive assignment lies above a minimal positive in its slice, and every negative assignment lies below a maximal negative. Agreement there forces agreement on all 1,024 original rows. This sufficiency is specific to the AND/OR branch after the signed exclusion.

For every positive and negative boundary row, at least one live physical wire must be true on the positive row and false on the negative row. Otherwise every monotone continuation fails that pair. This condition can be tested again when operands are retired. A stored boundary function can replace an identical available physical signal. Substitution preserves every boundary answer, so slice monotonicity again yields correctness everywhere. Gate inputs may use the opposite physical rail only when it is actually available.

For each one-vertex deletion, the remaining circuit has either no free complement or the complement of a surviving vertex. Up to relabelling, that distinguished vertex is adjacent or nonadjacent to the deleted one. Exhaustive physical searches exclude 15 gates in both cases. Consequently all ten zero pins in the final physical search can use a lower bound of 16. These higher pin bounds enter only the physical branch.

In the final primary search the first gate ranges over representatives under graph automorphisms fixing the distinguished vertex. The rest can be ordered by the pair consisting of the larger source index followed by the smaller one. Greedily taking the least ready pair gives this order, because every newly enabled gate reads the newly created highest-index wire. The selected first gate is exempt. Memoization includes signal identities, physical polarity availability, original wire positions and the last permitted ordering threshold. Hash tables also compare keys for equality.

The resulting 18-gate search returned no witness. The target has a verified 20-gate construction.

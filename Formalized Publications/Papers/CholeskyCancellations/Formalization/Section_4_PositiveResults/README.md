Section 4: positive results.

Reading order:

A_Theorem41Determinants.lean — almost-principal minors and the determinant formula; the forest theorem (Theorem 4.1): every ordering of a forest pattern is clean.
B_StripMachinery.lean — strip patterns and states (Definitions 4.3–4.5), end/second pivots, and clean continuations.
C_StripHelpers.lean — distance-one/two membership lemmas, game-graph append facts, Schur-entry computations, and the small strip state lemmas.
D_StripContinuation.lean — the strip state machine; `strips_perMatrix` (Theorem 4.8).
E_FanContinuation.lean — fan patterns and states, the fan state machine; `fans_perMatrix` (Theorem 4.8).
F_PeelingAndCycles.lean — peeling a vertex with at most one survivor neighbour; cycle/path infrastructure and longest paths.
G_ExistsPeelVertex.lean — every suitable graph has a peelable vertex.
H_OneTriangleSetup.lean — exactly-one-triangle and edge-disjoint-triangle predicates, index bookkeeping, and the long-path endpoint lemma, used by J_EdgeDisjointAndAssembly.lean.
I_OneTriangleContinuation.lean — the one-triangle state machine and clean apexes; `one_triangle_perMatrix` (Theorem 4.8).
J_EdgeDisjointAndAssembly.lean — chordal states, the edge-disjoint continuation, `edge_disjoint_perMatrix`, and the assembly `positives` (Theorem 4.8).

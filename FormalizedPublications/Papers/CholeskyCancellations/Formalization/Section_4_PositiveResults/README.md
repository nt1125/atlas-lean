# Section 4: positive results.

Reading order:

1. A_Theorem41Determinants.lean — almost-principal minors and the determinant formula; the forest theorem (Theorem 4.1): every ordering of a forest pattern is clean.
2. B_StripMachinery.lean — strip patterns and states (Definitions 4.3–4.5), end/second pivots, and clean continuations.
3. C_StripHelpers.lean — distance-one/two membership lemmas, game-graph append facts, Schur-entry computations, and the small strip state lemmas.
4. D_StripContinuation.lean — the strip state machine; `strips_perMatrix` (Theorem 4.8).
5. E_FanContinuation.lean — fan patterns and states, the fan state machine; `fans_perMatrix` (Theorem 4.8).
6. F_PeelingAndCycles.lean — peeling a vertex with at most one survivor neighbour; cycle/path infrastructure and longest paths.
7. G_ExistsPeelVertex.lean — every suitable graph has a peelable vertex.
8. H_OneTriangleSetup.lean — exactly-one-triangle and edge-disjoint-triangle predicates, index bookkeeping, and the long-path endpoint lemma, used by J_EdgeDisjointAndAssembly.lean.
9. I_OneTriangleContinuation.lean — the one-triangle state machine and clean apexes; `one_triangle_perMatrix` (Theorem 4.8).
10. J_EdgeDisjointAndAssembly.lean — chordal states, the edge-disjoint continuation, `edge_disjoint_perMatrix`, and the assembly `positives` (Theorem 4.8).
11. K_AdaptiveAndFixedOrderings.lean — Theorem 4.8 in the adaptive strategy form (`positives_adaptive`), and Remark 4.9's triangle: `K₃` lies in every class of Theorem 4.8 and has no fixed clean ordering (`positives_no_fixed_ordering`).

# Section 5: even counterexamples and order four.

Reading order:

1. A_Astar.lean — the order-four matrix `A*` (Theorem 5.1), refuting the first Schur-complement conjecture (Conjecture 2.26).
2. B_SmallOrders.lean — pattern/symbolic comparison helpers and clean orderings for triangles and four-vertex levels; Conjecture 1 at order three.
3. C_ExistsCleanFour.lean — every irreducible SPD 4 × 4 matrix has a clean ordering; Conjecture 1 holds at every order ≤ 4 (Theorem 5.2).
4. D_PairingLemma.lean — fixed-point-free involutions, candidate slots, pairing configurations (Lemma 5.5), and forced magnitudes.
5. E_M2mMatrix.lean — the `M_{2m}` matrices, their pair partners, entry computations, and no clean ordering at the curve point.
6. F_M2mPosDef.lean — weights, eigendecomposition, positive definiteness, the characteristic polynomial, the counterexample at every even order ≥ 6 (Theorem 5.8), and the refutation of the fill-graph conjecture (Conjecture 2.27).
7. G_ParameterCurve.lean — Remark 5.9: the curve has exactly one admissible root α(B) for each B in (0, 1), so Theorem 5.8 gives a one-parameter family of counterexamples; the endpoint behaviour.
8. H_AstarInFamily.lean — Remark 5.10: `A*`, normalised, relabeled and conjugated by a sign matrix, is the order-four member of the `M_{2m}` family; sign conjugation preserves the cancellation structure.

# Section 2: setting, vocabulary, and conjectures.

Reading order:

1. A_SchurComplement.lean — the survivor index type, `schurEntry`, `pivotEntry`, and the basic SPD facts (Schur complements stay SPD; 2 × 2 minors), used throughout.
2. B_PatternGraphs.lean — pattern, elimination-step, game, and fill graphs; orderings and committing prefixes; walks and fill paths.
3. C_Chordality.lean — simplicial and pendant vertices, perfect elimination orderings, chordal graphs, cut vertices, blocks and the block-cut graph, clique sums, and irreducibility.
4. D_CleanPivots.lean — Zeroes, cancellation graphs, covers, survivors, clean pivots and apexes, and the assembled Cholesky factor.
5. E_StrategyVocabulary.lean — clean orderings; the per-matrix existential and the adaptive-strategy notions (Definition 2.25).
6. F_ConjecturesAndFeasibility.lean — the two conjectures, slots, feasibility, realizability, partial correlations, and log-magnitudes; the conjectures are refuted in Section_5_EvenCounterexamplesAndOrderFour/.
7. G_FillGraphChordal.lean — Remark 2.11: the fill graph contains the pattern graph, is nonempty for connected patterns, has σ as a perfect elimination ordering and is chordal, and contains the factor pattern.
8. H_BlockDiagonal.lean — Remark 2.18: for a block-diagonal matrix, clean orderings of the blocks concatenate to a clean ordering, and the fill graph is the disjoint union of the blocks' fill graphs.
9. I_CoveringReformulation.lean — Remark 2.30: a matrix has no clean ordering iff its active slots spoil every ordering, and Conjecture 2.27 fails for a pattern iff some blocking family is realizable for it.

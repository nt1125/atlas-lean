# Accidental Cancellations in Cholesky Factorization — Paper and Lean Formalization

> **Layout note:** this `Readme.md` describes the Atlas-style re-layout at `FormalizedPublications/Papers/CholeskyCancellations/` (formalization split into per-section files under `Formalization/`). The original repository, with the buildable Lake project, is at <https://github.com/nt1125/CholeskyCancellations>.

A Lean 4 formalization of **[Accidental Cancellations in Cholesky Factorization](Papers/cholesky_cancellations.pdf)**
by Nam Trang and Meta AI.

> **Read the paper with its formalization:**
> [⬇ Download the interactive paper](https://raw.githubusercontent.com/nt1125/atlas-lean/main/FormalizedPublications/Papers/CholeskyCancellations/Papers/cholesky_cancellations_interactive.html)
> — a single page rendering the paper with a Lean box at every definition and result.
> Open the downloaded file in a browser (internet needed for the math rendering);
> it also opens directly from a local clone at [`Papers/cholesky_cancellations_interactive.html`](Papers/cholesky_cancellations_interactive.html).

Sparse Cholesky codes allocate storage from the symbolic fill pattern,
assuming no predicted-nonzero entry ever cancels. The paper asks whether
some ordering can always avoid cancellation, and answers no:
Conjecture 2 fails at order 4 and Conjecture 1 at every even order at
least 6, while forests, strips, fans, and two chordal classes are always
clean. Every result below is formalized in Lean alongside the
mathematics: the formalization is part of the presentation, not a
footnote.

## Formalization status

The paper's challenges and their Lean counterparts (short names; hover any
link for the full dotted path):

| | Paper result | Lean | Status |
|---|---|---|---|
| C1 | Conjecture 2.26 ([p. 11](Papers/cholesky_cancellations.pdf#page=11)): first-Schur conjecture | `first_schur_conjecture` in [F_ConjecturesAndFeasibility.lean](Formalization/Section_2_SettingVocabularyAndConjectures/F_ConjecturesAndFeasibility.lean#L48), refuted by `first_schur_conjecture_refuted` in [A_Astar.lean](Formalization/Section_5_EvenCounterexamplesAndOrderFour/A_Astar.lean#L390) | refuted in Lean (paper Theorem 5.1) |
| C2 | Conjecture 2.27 ([p. 11](Papers/cholesky_cancellations.pdf#page=11)): fill-graph conjecture | `fill_graph_conjecture` in [F_ConjecturesAndFeasibility.lean](Formalization/Section_2_SettingVocabularyAndConjectures/F_ConjecturesAndFeasibility.lean#L58), refuted by `fill_graph_conjecture_refuted` in [F_M2mPosDef.lean](Formalization/Section_5_EvenCounterexamplesAndOrderFour/F_M2mPosDef.lean#L1059) | refuted in Lean at every even order ≥ 6 (paper Theorem 5.8, `m2m_counterexample_all_orders`) |
| C3 | Theorem 4.1: forests, every ordering clean | `forest_clean` in [A_Theorem41Determinants.lean](Formalization/Section_4_PositiveResults/A_Theorem41Determinants.lean#L503) | proved, axiom-clean |
| C4 | Theorem 4.8: strips, fans, one-triangle, edge-disjoint triangles | `positives` in [J_EdgeDisjointAndAssembly.lean](Formalization/Section_4_PositiveResults/J_EdgeDisjointAndAssembly.lean#L321) (parts `strips_perMatrix`, `fans_perMatrix`, `one_triangle_perMatrix`, `edge_disjoint_perMatrix`, in the per-matrix form `PatternAdmitsPerMatrixCleanOrdering`); the paper's adaptive strategy form `positives_adaptive` in [K_AdaptiveAndFixedOrderings.lean](Formalization/Section_4_PositiveResults/K_AdaptiveAndFixedOrderings.lean#L36), through the equivalence `perMatrix_iff_adaptiveStrategy` in [J_AdaptiveBridge.lean](Formalization/Section_2_SettingVocabularyAndConjectures/J_AdaptiveBridge.lean#L433); no fixed ordering suffices for any class: `positives_no_fixed_ordering` in [K_AdaptiveAndFixedOrderings.lean](Formalization/Section_4_PositiveResults/K_AdaptiveAndFixedOrderings.lean#L263) | proved, axiom-clean |
| C5 | Theorem 5.1: Conjecture 2 fails at order 4 (`A*`) | `astar_counts` in [A_Astar.lean](Formalization/Section_5_EvenCounterexamplesAndOrderFour/A_Astar.lean#L366) | proved, axiom-clean |
| C6 | Theorem 5.2 ([p. 28](Papers/cholesky_cancellations.pdf#page=28)): Conjecture 1 for orders at most 4 | `clean_of_order_le_four` in [C_ExistsCleanFour.lean](Formalization/Section_5_EvenCounterexamplesAndOrderFour/C_ExistsCleanFour.lean#L457) | proved, axiom-clean |
| C7 | Lemma 5.5 ([p. 29](Papers/cholesky_cancellations.pdf#page=29)): Pairing Lemma | `pairing` in [D_PairingLemma.lean](Formalization/Section_5_EvenCounterexamplesAndOrderFour/D_PairingLemma.lean#L649) | proved, axiom-clean |
| C8 | Corollary 5.6 ([p. 30](Papers/cholesky_cancellations.pdf#page=30)): magnitudes forced | `magnitudes_forced` in [D_PairingLemma.lean](Formalization/Section_5_EvenCounterexamplesAndOrderFour/D_PairingLemma.lean#L678) | proved, axiom-clean |
| C9 | Theorem 5.8 ([p. 32](Papers/cholesky_cancellations.pdf#page=32)): Conjecture 1 fails at every even order at least 6 | `m2m_counterexample` (unconditional form: `m2m_counterexample_all_orders`) in [F_M2mPosDef.lean](Formalization/Section_5_EvenCounterexamplesAndOrderFour/F_M2mPosDef.lean#L953) | proved, axiom-clean |

All remaining definitions, propositions, lemmas, corollaries, and
examples of Sections 2–5 are likewise formalized in the files above
and in [Section_3_CoreLemmas](Formalization/Section_3_CoreLemmas/)
(Section 3), including the equivalence of the per-matrix and adaptive
strategy forms stated in Definition 2.25
([J_AdaptiveBridge.lean](Formalization/Section_2_SettingVocabularyAndConjectures/J_AdaptiveBridge.lean)).
Remarks 2.11, 2.18, 2.30, 4.9, 5.9 and 5.10 are formalized
too (the Lean boxes of the interactive paper say what each covers):
Remarks 2.11, 2.18 and 2.30 in
[G_FillGraphChordal.lean](Formalization/Section_2_SettingVocabularyAndConjectures/G_FillGraphChordal.lean),
[H_BlockDiagonal.lean](Formalization/Section_2_SettingVocabularyAndConjectures/H_BlockDiagonal.lean)
and [I_CoveringReformulation.lean](Formalization/Section_2_SettingVocabularyAndConjectures/I_CoveringReformulation.lean),
the triangle witness of Remark 4.9 in
[K_AdaptiveAndFixedOrderings.lean](Formalization/Section_4_PositiveResults/K_AdaptiveAndFixedOrderings.lean)
(its five-vertex witness is checked by the script in
[Appendix_FixedOrderingWitnesses](Formalization/Appendix_FixedOrderingWitnesses/)),
and Remarks 5.9 and 5.10 in
[G_ParameterCurve.lean](Formalization/Section_5_EvenCounterexamplesAndOrderFour/G_ParameterCurve.lean)
and [H_AstarInFamily.lean](Formalization/Section_5_EvenCounterexamplesAndOrderFour/H_AstarInFamily.lean).
Every formalized result is a proved theorem, and
the two conjectures (C1, C2) are stated and refuted in Lean, as in the paper (Theorems 5.1 and 5.8).

## Contents

- [Paper (PDF)](Papers/cholesky_cancellations.pdf) · [Paper with Lean boxes](Papers/cholesky_cancellations_interactive.html)
- 1. Introduction ([PDF p. 1](Papers/cholesky_cancellations.pdf#page=1))
- 2. Setting, vocabulary, and conjectures ([PDF p. 6](Papers/cholesky_cancellations.pdf#page=6))
    - Core definitions and Section 2 results. [Section_2_SettingVocabularyAndConjectures](Formalization/Section_2_SettingVocabularyAndConjectures/)
- 3. Core lemmas ([PDF p. 13](Papers/cholesky_cancellations.pdf#page=13))
    - Exchange through Monotone. [Section_3_CoreLemmas](Formalization/Section_3_CoreLemmas/)
- 4. Positive results ([PDF p. 19](Papers/cholesky_cancellations.pdf#page=19))
    - Forests, strips, fans. [Section_4_PositiveResults](Formalization/Section_4_PositiveResults/)
- 5. Even counterexamples and order four ([PDF p. 27](Papers/cholesky_cancellations.pdf#page=27))
    - `A*`, order four, Pairing Lemma, `M_{2m}`. [Section_5_EvenCounterexamplesAndOrderFour](Formalization/Section_5_EvenCounterexamplesAndOrderFour/)
- 6–8 and appendices: consequences, open problems, computational protocol — paper only (no Lean content).

## Trust

* Library (`Formalization/`) contains no `sorry`, `axiom`, `native_decide`,
  `unsafe`, `partial def`, or `Float` — no holes, period. Unproved
  results are stated as `Prop` definitions, which assert nothing.
* Top-level proofs depend only on `propext`, `Classical.choice`,
  `Quot.sound`.
* For readers experienced with Lean, `Comparator/` holds the comparator
  challenge `cholesky_cancellations_comparator.lean` and its configuration
  `cholesky_cancellations_comparator.json`. The challenge restates the
  paper's definitions independently of the solution (it imports only
  Mathlib) and states the paper's main results with `sorry` proofs; the
  configuration lists those results under `theorem_names` and the
  definitions under `definition_names`. For the full check, run the
  comparator as instructed in
  [Validating a Lean Proof](https://lean-lang.org/doc/reference/4.35.0/ValidatingProofs/#validating-comparator):
  it checks that the solution proves exactly these statements, with the
  same definitions, using only the permitted axioms.

## Building

```
lake exe cache get
```
fetches prebuilt Mathlib oleans. Elaborate `Formalization/` in dependency order with `lake env lean --root=Formalization`, writing oleans to a directory on `LEAN_PATH` (root module `CholeskyCancellations` last). `Formalization/` uses Atlas-style unprefixed imports and has no Lake lib; see [lakefile.toml](../../../lakefile.toml).

## Authorship

The paper was written by Nam Trang with Muse Spark via meta.ai, and reviewed by Paul Bendich and Patrick Tam.

The formalization was produced and reviewed by Nam Trang, using Muse Code.

## Versions

Current version pinned at the top level of this repository: Lean v4.35.0 and Mathlib v4.35.0 in [lean-toolchain](../../../lean-toolchain), [lakefile.toml](../../../lakefile.toml), and [lake-manifest.json](../../../lake-manifest.json).

**Formalization published October 31, 2026.**

Originally verified with Lean v4.34.0 and Mathlib v4.34.0 (Mathlib rev `5ed2965256430c3649e86755f9576b54eca72435`, pinned at scaffolding). Re-verified with:

- Lean v4.35.0
- Mathlib v4.35.0
- MathlibExt v2

The formalization does not import MathlibExt, so MathlibExt v2 is listed as the environment version (Atlas convention); the substantive check is Lean/Mathlib v4.35.0.

## License

Apache-2.0 — see [LICENSE](LICENSE).

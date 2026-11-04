/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Section_2_SettingVocabularyAndConjectures.D_CleanPivots

/-! # Clean orderings and strategy vocabulary (paper Section 2)

Clean orderings, the factor-pattern characterisation, one fixed ordering for all realizations (`IsFixedOrderingFor`), the per-matrix existential, the Schur matrix `schurMatrix`, and the adaptive-strategy notions (paper Definition 2.25).
-/

open scoped Matrix

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): vertices `Fin n`, SPD = `Matrix.PosDef`, levels `Finset (Fin n)`, pivot-order list orderings, Schur entries through `schurEntry` only. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}



/-- `IsCleanOrdering A σ`: every predicted-nonzero position is nonzero
at its committing level (paper Definition 2.24, `def:clean`), the
factor notion of cleanliness. -/
def IsCleanOrdering (A : Matrix (Fin n) (Fin n) ℝ) (σ : List (Fin n)) :
    Prop :=
  ∀ j k : Fin n, PredictedNonzero A σ j k →
    schurEntry A (prefixSet σ j k) j k ≠ 0



/-- `clean_iff_factor_pattern`: cleanliness is the equality
`Gᴸ_σ = G⁺_σ` of patterns (the equivalence recorded in paper
Definition 2.24, `def:clean`). Proved: factor-pattern adjacency is
nonvanishing at the committing level, and the containment
`Gᴸ_σ ⊆ G⁺_σ` is `numeric_le_symbolic`. -/
theorem clean_iff_factor_pattern (hA : A.PosDef)
    (σ : List (Fin n)) (hσ : IsOrdering σ) :
    (IsCleanOrdering A σ ↔ factorPattern A σ = fillGraph A σ) := by
  have hfact : ∀ j k : Fin n, (factorPattern A σ).Adj j k →
      schurEntry A (prefixSet σ j k) j k ≠ 0 := by
    intro j k h
    have hadj : j ≠ k ∧ (schurEntry A (prefixSet σ j k) j k ≠ 0
        ∨ schurEntry A (prefixSet σ k j) k j ≠ 0) := by
      simpa [factorPattern, SimpleGraph.fromRel_adj] using h
    rcases hadj.2 with h' | h'
    · exact h'
    · rw [prefixSet_comm, schurEntry_symm hA] at h'
      exact h'
  constructor
  · intro hclean
    apply SimpleGraph.ext
    funext j k
    apply propext
    constructor
    · intro h
      exact (numeric_le_symbolic hA).2 σ hσ j k h
    · intro h
      have hne : schurEntry A (prefixSet σ j k) j k ≠ 0 := hclean j k h
      simp [factorPattern, SimpleGraph.fromRel_adj, h.ne, hne]
  · intro heq j k hpred
    have h : (factorPattern A σ).Adj j k := heq.symm ▸ hpred
    exact hfact j k h



/-- `IsFixedOrderingFor G σ`: one ordering chosen from the pattern
alone, clean for every SPD realization (paper Definition 2.25,
`def:strategy`). -/
def IsFixedOrderingFor (G : SimpleGraph (Fin n)) (σ : List (Fin n)) : Prop :=
  IsOrdering σ ∧ ∀ A : Matrix (Fin n) (Fin n) ℝ,
    A.PosDef → patternGraph A = G → IsCleanOrdering A σ



/-- `PatternAdmitsPerMatrixCleanOrdering G`: for every SPD
realization some (hence possibly matrix-dependent) ordering is
clean. This is the per-matrix existential reading of the paper's
"admits an adaptive clean ordering" (paper Definition 2.25,
`def:strategy`) — not the paper's strategy reading. It is
deliberately named for what it is: the ordering `σ` may be chosen
after seeing all of `A`, with no requirement that its pivots be
produced by one pivot-choice rule. Although the paper's Theorem
4.8 is phrased as "Conjecture 1 holds for …", Definition 2.25
reads that phrase in the adaptive strategy sense; `positives`
proves only this weaker per-matrix form. For the paper's
strategy form, see `PatternAdmitsAdaptiveStrategy`:
it is a priori more restrictive (a strategy must make the same next
choice for matrices agreeing up to the current level); whether it
is strictly stronger is not established here, and the
development does not prove it for any class. -/
def PatternAdmitsPerMatrixCleanOrdering (G : SimpleGraph (Fin n)) :
    Prop :=
  ∀ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef → patternGraph A = G →
    ∃ σ : List (Fin n), IsOrdering σ ∧ IsCleanOrdering A σ



/-- `schurMatrix A S`: the current Schur complement `A/A_S` as a
full matrix on `Fin n`, with entries `schurEntry A S j k` — the
only data an adaptive strategy may consult at level `S` (paper
Definition 2.25, `def:strategy`). -/
noncomputable def schurMatrix (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun j k => schurEntry A S j k



/-- `AdaptiveCleanStrategy G next`: `next` is an adaptive clean
strategy for the pattern `G` (paper Definition 2.25,
`def:strategy`). At each level `S`, `next` chooses the next pivot
as a function of `S` and the current Schur complement
`schurMatrix A S` alone — never of `A` itself — so two matrices
with the same Schur complement at `S` get the same next pivot
(consistency across matrices agreeing up to `S`). An ordering
`σ` follows `next` when every pivot `p` of `σ` is the choice
`next` makes at the level of the pivots preceding `p`. -/
def AdaptiveCleanStrategy (G : SimpleGraph (Fin n))
    (next : Finset (Fin n) → Matrix (Fin n) (Fin n) ℝ → Fin n) :
    Prop :=
  ∀ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef → patternGraph A = G →
    ∃ σ : List (Fin n), IsOrdering σ ∧ IsCleanOrdering A σ ∧
      ∀ (l₁ : List (Fin n)) (p : Fin n) (l₂ : List (Fin n)),
        σ = l₁ ++ p :: l₂ →
          p = next l₁.toFinset (schurMatrix A l₁.toFinset)



/-- `PatternAdmitsAdaptiveStrategy G`: some adaptive clean strategy
(as in `AdaptiveCleanStrategy`) yields a clean ordering for every
SPD realization of `G` — the paper's Definition 2.25 reading of
"admits an adaptive clean ordering". This is the paper's strategy
reading, a priori more restrictive than the per-matrix form;
`PatternAdmitsPerMatrixCleanOrdering` is what `positives`
proves. -/
def PatternAdmitsAdaptiveStrategy (G : SimpleGraph (Fin n)) : Prop :=
  ∃ next : Finset (Fin n) → Matrix (Fin n) (Fin n) ℝ → Fin n,
    AdaptiveCleanStrategy G next



/-- A genuine adaptive strategy yields a per-matrix clean ordering
(forget the consistency condition). -/
theorem adaptiveStrategy_implies_perMatrix {G : SimpleGraph (Fin n)}
    (h : PatternAdmitsAdaptiveStrategy G) :
    PatternAdmitsPerMatrixCleanOrdering G := by
  obtain ⟨next, hstrat⟩ := h
  intro A hA hG
  obtain ⟨σ, hord, hclean, -⟩ := hstrat A hA hG
  exact ⟨σ, hord, hclean⟩

end CholeskyCancellations

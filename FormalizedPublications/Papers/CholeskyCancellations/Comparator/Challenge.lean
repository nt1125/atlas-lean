/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/
import Mathlib
import Definitions

/-!
# Challenge: accidental cancellations in Cholesky factorization

This file states the main results of the paper for independent audit.
It must NOT import the solution (`Formalization/`): the only imports
are Mathlib and the companion `Definitions.lean` in this same folder,
which restates the paper's definitions independently (Mathlib-only).
An auditor checks faithfulness by comparing these statements against
the paper and against the solution's proofs of the same-named theorems
in `Formalization/`. Every proof here is `sorry`, by design.
-/

open scoped Matrix

namespace CholeskyCancellations

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {m : ℕ} {a b : ℝ}

/-- Paper Theorem 4.8 (per-matrix form): strip, fan, and chordal one-triangle / edge-disjoint-triangle patterns admit a clean ordering for every matrix with that pattern. -/
theorem positives :
    (∀ {n : ℕ} (G : SimpleGraph (Fin n)), IsStripPattern G →
      PatternAdmitsPerMatrixCleanOrdering G)
    ∧ (∀ {n : ℕ} (G : SimpleGraph (Fin n)), IsFanPattern G →
        PatternAdmitsPerMatrixCleanOrdering G)
    ∧ (∀ {n : ℕ} (G : SimpleGraph (Fin n)),
        IsChordal G → ExactlyOneTriangle G → PatternAdmitsPerMatrixCleanOrdering G)
    ∧ (∀ {n : ℕ} (G : SimpleGraph (Fin n)),
        IsChordal G → G.cliqueNum ≤ 3 → TrianglesEdgeDisjoint G →
          PatternAdmitsPerMatrixCleanOrdering G) := by
  sorry


/-- Paper Theorem 5.2: every irreducible SPD matrix of order at most 4 has a clean ordering. -/
theorem clean_of_order_le_four : ∀ {n : ℕ}, n ≤ 4 →
    ∀ A : Matrix (Fin n) (Fin n) ℝ,
    A.PosDef → IsIrreducible A →
      ∃ σ : List (Fin n), IsOrdering σ ∧ IsCleanOrdering A σ := by
  sorry


/-- Paper Theorem 5.1 / Conjecture 2.26 refuted: the order-4 matrix A* has no clean ordering, so the first Schur-complement conjecture is false. -/
theorem first_schur_conjecture_refuted : ¬ first_schur_conjecture := by
  sorry


/-- Paper Theorem 5.8: at every even order 2m (m >= 3) there is an irreducible SPD matrix with no clean ordering. -/
theorem m2m_counterexample_all_orders (m : ℕ) (hm : 3 ≤ m) :
    ∃ A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ,
      A.PosDef ∧ IsIrreducible A ∧
        ∀ σ : List (Fin (2 * m)), IsOrdering σ →
          ¬ IsCleanOrdering A σ := by
  sorry


/-- Paper Conjecture 2.27 refuted: the fill-graph conjecture is false. -/
theorem fill_graph_conjecture_refuted : ¬ fill_graph_conjecture := by
  sorry

end CholeskyCancellations

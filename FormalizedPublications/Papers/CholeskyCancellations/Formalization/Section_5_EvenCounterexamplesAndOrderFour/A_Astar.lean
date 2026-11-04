/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Section_4_PositiveResults.J_EdgeDisjointAndAssembly

/-! # The `A*` counterexample (paper Section 5)

The order-four matrix `astar` (paper Theorem 5.1): positive definite, irreducible, with no clean ordering whose first Schur complement is clean — refuting the first Schur-complement conjecture (Conjecture 2.26).
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as the Section 2 files; concrete matrices are on `Fin 4` and `Fin (2 * m)` with pair/parity read from `Finset` levels and `Fin.val` division as in the paper's `P_k = {2k, 2k+1}` indexing. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- `astar`: the order-four matrix
`[[4,-2,-2,-1],[-2,4,1,2],[-2,1,4,2],[-1,2,2,4]]` (paper
Theorem 5.1, `thm:Astar`). -/
def astar : Matrix (Fin 4) (Fin 4) ℝ :=
  !![4, -2, -2, -1; -2, 4, 1, 2; -2, 1, 4, 2; -1, 2, 2, 4]



/-- `astarP`: the eigenbasis matrix for `astar`, with columns
`(1,-1,-1,-1)`, `(1,1,1,-1)`, `(0,1,-1,0)` and `(1,0,0,1)`, of
eigenvalues `9, 1, 3, 3`. Its columns are mutually orthogonal. -/
def astarP : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of ![
  ![1, 1, 0, 1],
  ![-1, 1, 1, 0],
  ![-1, 1, -1, 0],
  ![-1, -1, 0, 1]]



/-- The eigenbasis matrix for `astar` has determinant `-8`. -/
theorem astarP_det : astarP.det = -8 := by
  norm_num [astarP, Matrix.det_succ_row_zero, Fin.sum_univ_four,
    Fin.sum_univ_three, Fin.sum_univ_two, Fin.succAbove]



/-- `astar` is positive definite, by the orthogonal eigenbasis
congruence with diagonal weights `9/4, 1/4, 3/2, 3/2`. -/
theorem astar_posDef : astar.PosDef := by
  have hdet : IsUnit astarP.det := by
    rw [astarP_det]
    norm_num
  have hPunit : IsUnit astarP := (Matrix.isUnit_iff_isUnit_det astarP).mpr hdet
  have hD : (Matrix.diagonal ![(9 : ℝ) / 4, 1 / 4, 3 / 2, 3 / 2]).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num
  have hcong := hD.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit hPunit)
  have hfact : astar
      = astarP * Matrix.diagonal ![(9 : ℝ) / 4, 1 / 4, 3 / 2, 3 / 2] *
          astarP.conjTranspose := by
    have ht : astarP.conjTranspose = astarP.transpose := by
      ext i j
      simp [Matrix.conjTranspose]
    rw [ht]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, astar, astarP, Fin.sum_univ_four,
        Matrix.vecMul_diagonal]
  rwa [hfact]



/-- The characteristic polynomial of `astar` is
`(X-9)(X-3)^2(X-1)`, by similarity to the diagonal eigenvalue
matrix through `astarP`. -/
theorem astar_charpoly : astar.charpoly
    = (Polynomial.X - Polynomial.C 9) * (Polynomial.X - Polynomial.C 3) ^ 2
      * (Polynomial.X - Polynomial.C 1) := by
  have hdet : IsUnit astarP.det := by
    rw [astarP_det]
    norm_num
  have hAP : astar * astarP = astarP * Matrix.diagonal ![9, 1, 3, 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, astar, astarP, Fin.sum_univ_four]
  have hAeq : astar
      = astarP * Matrix.diagonal ![9, 1, 3, 3] * astarP⁻¹ := by
    calc astar = astar * astarP * astarP⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = astarP * Matrix.diagonal ![9, 1, 3, 3] * astarP⁻¹ := by
          rw [hAP]
  set U : (Matrix (Fin 4) (Fin 4) ℝ)ˣ := Matrix.nonsingInvUnit astarP hdet with hUdef
  have hchar : astar.charpoly = (Matrix.diagonal ![9, 1, 3, 3]).charpoly := by
    have h := Matrix.charpoly_units_conj U (Matrix.diagonal ![9, 1, 3, 3])
    rw [hAeq]
    exact h
  rw [hchar, Matrix.charpoly_diagonal]
  simp [Fin.prod_univ_four]
  ring



theorem astar_entry_ne_zero {j k : Fin 4} (hjk : j ≠ k) : astar j k ≠ 0 := by
  fin_cases j <;> fin_cases k <;> simp_all [astar]



theorem astar_pattern_adj {j k : Fin 4} (hjk : j ≠ k) :
    (patternGraph astar).Adj j k := by
  simp only [patternGraph, SimpleGraph.fromRel_adj]
  exact ⟨hjk, Or.inl (astar_entry_ne_zero hjk)⟩



theorem astar_schurEntry_singleton {p j k : Fin 4} (hj : j ≠ p) (hk : k ≠ p) :
    schurEntry astar {p} j k
      = astar j k - astar j p * astar k p / astar p p := by
  have hj' : j ∉ insert p (∅ : Finset (Fin 4)) := by simp [hj]
  have hk' : k ∉ insert p (∅ : Finset (Fin 4)) := by simp [hk]
  have h := schur_quotient astar_posDef ∅ p (by simp) j k hj' hk'
  simp only [Finset.insert_empty] at h
  rw [h]
  simp [pivotEntry, schurEntry_empty]



/-- No ordering of `astar` has a clean first Schur complement:
the first pivot always cancels the opposite pair. -/
theorem astar_not_firstSchurClean :
    ∀ σ : List (Fin 4), IsOrdering σ → ¬ FirstSchurClean astar σ := by
  intro σ hσ hclean
  obtain ⟨p, l, rfl⟩ : ∃ p l, σ = p :: l := by
    cases σ with
    | nil => simp [IsOrdering] at hσ
    | cons p l => exact ⟨p, l, rfl⟩
  have hgame : ∀ {j k : Fin 4}, j ≠ k →
      (gameGraph (patternGraph astar) [p]).Adj j k := by
    intro j k hjk
    have hgg : gameGraph (patternGraph astar) [p]
        = elimStep (patternGraph astar) p := by
      simp [gameGraph]
    rw [hgg]
    exact elimStep_adj_of_adj _ p j k (astar_pattern_adj hjk)
  fin_cases p
  · exact (hclean 0 l rfl 1 2 (by norm_num) (by norm_num) (hgame (by norm_num)))
      (by rw [astar_schurEntry_singleton (by norm_num) (by norm_num)]; norm_num [astar])
  · exact (hclean 1 l rfl 0 3 (by norm_num) (by norm_num) (hgame (by norm_num)))
      (by rw [astar_schurEntry_singleton (by norm_num) (by norm_num)]; norm_num [astar])
  · exact (hclean 2 l rfl 0 3 (by norm_num) (by norm_num) (hgame (by norm_num)))
      (by rw [astar_schurEntry_singleton (by norm_num) (by norm_num)]; norm_num [astar])
  · exact (hclean 3 l rfl 1 2 (by norm_num) (by norm_num) (hgame (by norm_num)))
      (by rw [astar_schurEntry_singleton (by norm_num) (by norm_num)]; norm_num [astar])



/-- The partnership involution `(0 3)(1 2)` on the four indices of
`astar`. -/
def astarPartner (x : Fin 4) : Fin 4 := ![3, 2, 1, 0] x



theorem astarPartner_involutive : Function.Involutive astarPartner := by
  intro x
  fin_cases x <;> rfl



theorem astarPartner_ne_self (x : Fin 4) : astarPartner x ≠ x := by
  fin_cases x <;> decide



/-- In the first Schur complement of `astar`, the unique zero among
survivor pairs is the partnership pair opposite the pivot's pair. -/
theorem astar_schurEntry_singleton_eq_zero {p j k : Fin 4}
    (hj : j ≠ p) (hk : k ≠ p) (hjk : j ≠ k) :
    schurEntry astar {p} j k = 0 ↔ astarPartner j = k ∧ astarPartner p ≠ j := by
  rw [astar_schurEntry_singleton hj hk]
  fin_cases p <;> fin_cases j <;> fin_cases k <;>
    simp_all [astar, astarPartner] <;> norm_num



/-- After a partnership first two pivots in `astar`, the final
survivor entry is nonzero (the refill in Theorem 5.1). -/
theorem astar_schurEntry_pair_ne_zero {p q j k : Fin 4}
    (hpq : q = astarPartner p) (hpj : p ≠ j) (hpk : p ≠ k)
    (hqj : q ≠ j) (hqk : q ≠ k) (hjk : j ≠ k) :
    schurEntry astar {p, q} j k ≠ 0 := by
  have hform : schurEntry astar (insert q {p}) j k
      = schurEntry astar {p} j k
        - schurEntry astar {p} j q * schurEntry astar {p} k q
          / schurEntry astar {p} q q := by
    have hj' : j ∉ insert q ({p} : Finset (Fin 4)) := by
      simp [Finset.mem_insert, hqj.symm, hpj.symm]
    have hk' : k ∉ insert q ({p} : Finset (Fin 4)) := by
      simp [Finset.mem_insert, hqk.symm, hpk.symm]
    have hqp : q ≠ p :=
      fun h => astarPartner_ne_self p (hpq.symm.trans h)
    have h := schur_quotient astar_posDef {p} q (by simp [hqp]) j k hj' hk'
    rw [h]
    rfl
  have hset : ({p, q} : Finset (Fin 4)) = insert q {p} := by
    rw [Finset.pair_comm]
  rw [hset, hform]
  fin_cases p <;> fin_cases q <;> fin_cases j <;> fin_cases k <;>
    simp_all [astarPartner, astar_schurEntry_singleton] <;>
    norm_num [astar]



/-- Every distinct pair is predicted nonzero in `astar`, whose
pattern graph is complete. -/
theorem astar_predicted {σ : List (Fin 4)} {x y : Fin 4} (hxy : x ≠ y) :
    PredictedNonzero astar σ x y := by
  rw [PredictedNonzero, fillGraph_adj_iff]
  have h0 : (gameGraph (patternGraph astar) ([] : List (Fin 4))).Adj x y :=
    astar_pattern_adj hxy
  have h := gameGraph_adj_mono_append (patternGraph astar) []
    (prefixList σ x y) x y h0
  simpa using h



/-- For a four-term ordering of `astar`, cleanliness is exactly
that the second pivot is the first pivot's partner. -/
theorem astar_isClean_cons_iff {p q j k : Fin 4}
    (hpq : p ≠ q) (hpj : p ≠ j) (hpk : p ≠ k)
    (hqj : q ≠ j) (hqk : q ≠ k) (hjk : j ≠ k) :
    IsCleanOrdering astar [p, q, j, k] ↔ q = astarPartner p := by
  have hUniv : ({p, q, j, k} : Finset (Fin 4)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin, Finset.card_eq_four]
    exact ⟨p, q, j, k, hpq, hpj, hpk, hqj, hqk, hjk, rfl⟩
  have hlab : ∀ x : Fin 4, x = p ∨ x = q ∨ x = j ∨ x = k := by
    intro x
    have h : x ∈ ({p, q, j, k} : Finset (Fin 4)) := by rw [hUniv]; simp
    simpa using h
  have hpref_qj : prefixSet [p, q, j, k] q j = {p} := by
    simp_all [prefixSet, prefixList]
  have hpref_qk : prefixSet [p, q, j, k] q k = {p} := by
    simp_all [prefixSet, prefixList]
  constructor
  · intro hclean
    have hqj_ne : schurEntry astar {p} q j ≠ 0 := by
      have h := hclean q j (astar_predicted hqj)
      rwa [hpref_qj] at h
    have hqk_ne : schurEntry astar {p} q k ≠ 0 := by
      have h := hclean q k (astar_predicted hqk)
      rwa [hpref_qk] at h
    by_contra hpq'
    have hpartner_mem : astarPartner q = p ∨ astarPartner q = q ∨
        astarPartner q = j ∨ astarPartner q = k := hlab _
    rcases hpartner_mem with h | h | h | h
    · apply hpq'
      have hinv := astarPartner_involutive q
      rw [h] at hinv
      exact hinv.symm
    · exact astarPartner_ne_self q h
    · apply hqj_ne
      rw [astar_schurEntry_singleton_eq_zero (Ne.symm hpq) (Ne.symm hpj) hqj]
      exact ⟨h, fun hpj_eq => hpq' hpj_eq.symm⟩
    · apply hqk_ne
      rw [astar_schurEntry_singleton_eq_zero (Ne.symm hpq) (Ne.symm hpk) hqk]
      exact ⟨h, fun hpk_eq => hpq' hpk_eq.symm⟩
  · intro hpq_eq x y hpred
    have hxy : x ≠ y := hpred.ne
    have hqj_ne : schurEntry astar {p} q j ≠ 0 := by
      intro hz
      have hzero := (astar_schurEntry_singleton_eq_zero
        (Ne.symm hpq) (Ne.symm hpj) hqj).mp hz
      exact hzero.2 hpq_eq.symm
    have hqk_ne : schurEntry astar {p} q k ≠ 0 := by
      intro hz
      have hzero := (astar_schurEntry_singleton_eq_zero
        (Ne.symm hpq) (Ne.symm hpk) hqk).mp hz
      exact hzero.2 hpq_eq.symm
    have hfinal : schurEntry astar {p, q} j k ≠ 0 :=
      astar_schurEntry_pair_ne_zero hpq_eq hpj hpk hqj hqk hjk
    rcases hlab x with hx | hx | hx | hx <;>
      rcases hlab y with hy | hy | hy | hy <;> rw [hx, hy] at hxy ⊢
    · exact absurd rfl hxy
    · have hentry := astar_entry_ne_zero hxy
      simp_all [prefixSet, prefixList, schurEntry_empty]
    · have hentry := astar_entry_ne_zero hxy
      simp_all [prefixSet, prefixList, schurEntry_empty]
    · have hentry := astar_entry_ne_zero hxy
      simp_all [prefixSet, prefixList, schurEntry_empty]
    · have hentry := astar_entry_ne_zero hxy
      simp_all [prefixSet, prefixList, schurEntry_empty]
    · exact absurd rfl hxy
    · rwa [hpref_qj]
    · rwa [hpref_qk]
    · have hentry := astar_entry_ne_zero hxy
      simp_all [prefixSet, prefixList, schurEntry_empty]
    · have hpre : prefixSet [p, q, j, k] j q = {p} := by
        simp_all [prefixSet, prefixList]
      rw [hpre, schurEntry_symm astar_posDef]
      exact hqj_ne
    · exact absurd rfl hxy
    · have hpre : prefixSet [p, q, j, k] j k = {p, q} := by
        simp_all [prefixSet, prefixList]
      rwa [hpre]
    · have hentry := astar_entry_ne_zero hxy
      simp_all [prefixSet, prefixList, schurEntry_empty]
    · have hpre : prefixSet [p, q, j, k] k q = {p} := by
        simp_all [prefixSet, prefixList]
      rw [hpre, schurEntry_symm astar_posDef]
      exact hqk_ne
    · have hpre : prefixSet [p, q, j, k] k j = {p, q} := by
        simp_all [prefixSet, prefixList]
      rw [hpre, schurEntry_symm astar_posDef]
      exact hfinal
    · exact absurd rfl hxy



/-- Exactly eight orderings of `astar` are clean. -/
theorem astar_clean_orderings_ncard :
    {σ : List (Fin 4) | IsOrdering σ ∧ IsCleanOrdering astar σ}.ncard = 8 := by
  have hset : {σ : List (Fin 4) | IsOrdering σ ∧ IsCleanOrdering astar σ}
      = ↑({[0, 3, 1, 2], [0, 3, 2, 1], [3, 0, 1, 2], [3, 0, 2, 1],
          [1, 2, 0, 3], [1, 2, 3, 0], [2, 1, 0, 3], [2, 1, 3, 0]} :
          Finset (List (Fin 4))) := by
    ext σ
    constructor
    · rintro ⟨hord, hclean⟩
      obtain ⟨p, q, j, k, rfl⟩ := List.length_eq_four.mp hord.2
      have hp_not := (List.nodup_cons.mp hord.1).1
      have hnd2 := (List.nodup_cons.mp hord.1).2
      have hq_not := (List.nodup_cons.mp hnd2).1
      have hnd3 := (List.nodup_cons.mp hnd2).2
      have hj_not := (List.nodup_cons.mp hnd3).1
      simp only [List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hp_not hq_not hj_not
      obtain ⟨hpq, hpj, hpk⟩ := hp_not
      obtain ⟨hqj, hqk⟩ := hq_not
      have hjk : j ≠ k := hj_not
      have hpq_eq : q = astarPartner p :=
        (astar_isClean_cons_iff hpq hpj hpk hqj hqk hjk).mp hclean
      fin_cases p <;>
        norm_num [astarPartner] at hpq_eq <;> subst hpq_eq <;>
        fin_cases j <;> fin_cases k <;> simp_all
    · intro hσ
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hσ
      rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        refine ⟨by norm_num [IsOrdering, List.nodup_cons], ?_⟩ <;>
        · rw [astar_isClean_cons_iff (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num)]
          rfl
  rw [hset, Set.ncard_coe_finset]
  decide



/-- `astar_counts`: `A*` is SPD with spectrum `{9, 3, 3, 1}` (as
its characteristic factorization), no ordering has a clean first
Schur complement, and exactly 8 of its orderings are clean — so
Conjecture 2 fails at order 4 while Conjecture 1 survives it by
refill (paper Theorem 5.1, `thm:Astar`). -/
theorem astar_counts :
    astar.PosDef ∧
      astar.charpoly
        = (Polynomial.X - Polynomial.C 9) * (Polynomial.X - Polynomial.C 3) ^ 2
          * (Polynomial.X - Polynomial.C 1) ∧
      (∀ σ : List (Fin 4), IsOrdering σ → ¬ FirstSchurClean astar σ) ∧
      {σ : List (Fin 4) | IsOrdering σ ∧ IsCleanOrdering astar σ}.ncard = 8 :=
  ⟨astar_posDef, astar_charpoly, astar_not_firstSchurClean,
    astar_clean_orderings_ncard⟩



/-- `astar` is irreducible: every off-diagonal entry is nonzero. -/
theorem astar_irreducible : IsIrreducible astar := by
  intro V₁ V₂ hV₁ hV₂ hdisj _
  obtain ⟨i, hi⟩ := hV₁
  obtain ⟨j, hj⟩ := hV₂
  have hij : i ≠ j := fun h => (Finset.disjoint_left.mp hdisj hi) (h ▸ hj)
  exact ⟨i, hi, j, hj, astar_entry_ne_zero hij⟩



/-- The first Schur-complement conjecture (paper Conjecture 2.26,
`conj:2`) is false, by `astar` (paper Theorem 5.1, `thm:Astar`). -/
theorem first_schur_conjecture_refuted : ¬ first_schur_conjecture := by
  intro h
  obtain ⟨σ, hσord, hclean⟩ := h astar astar_counts.1 astar_irreducible
  exact astar_counts.2.2.1 σ hσord hclean

end CholeskyCancellations

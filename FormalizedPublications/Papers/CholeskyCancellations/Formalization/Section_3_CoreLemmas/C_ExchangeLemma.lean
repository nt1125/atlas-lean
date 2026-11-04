/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.TakeWhile
import Section_3_CoreLemmas.B_CleanApexAndTriangle

/-! # Exchange Lemma (paper Section 3)

The exchange step of the Triangle Lemma at a general level (paper Lemma 3.1): if apex `u` zeroes `(j, k)` and `schurEntry A S u k ≠ 0`, then apex `j` does not zero `(u, k)`. It is preceded by the `2 × 2` minor positivity (`schurEntry_two_mul_sub_pos`) its proof uses, which is also a Section 2-only fact.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as the Section 2 files; graph classes are predicates on `SimpleGraph (Fin n)` patterns and cleanliness is quantified per SPD realization through `PatternAdmitsPerMatrixCleanOrdering`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- The `2 × 2` positivity of a Schur complement, in entry form. -/
theorem schurEntry_two_mul_sub_pos {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (S : Finset (Fin n))
    {j k : Fin n} (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    0 < schurEntry A S j j * schurEntry A S k k
      - schurEntry A S j k * schurEntry A S k j := by
  have hne : (⟨j, Finset.mem_compl.mpr hj⟩ : Survivors S)
      ≠ ⟨k, Finset.mem_compl.mpr hk⟩ := by simp [hjk]
  have hm := posDef_two_mul_sub_pos (schurSet_posDef hA S) hne
  rwa [schurEntry_eq S hj hj, schurEntry_eq S hk hk,
    schurEntry_eq S hj hk, schurEntry_eq S hk hj]



/-- The exchange step of the Triangle Lemma at a general level: if
apex `u` zeroes the pair `(j, k)`, apex `j` does not zero `(u, k)`
(paper Lemma 3.1, `lem:exchange`, at level `S`). This is the paper's
statement: the hypothesis is the paper's `A_{uk} ≠ 0` (here
`schurEntry A S u k ≠ 0`), with `u, j, k` distinct survivors. In
particular no `schurEntry A S j k ≠ 0` hypothesis is assumed: the
`jk = 0` case is handled as in the paper's proof (then the
conclusion reduces to `uk ≠ 0`), not excluded. Note the paper
hypothesis is not redundant: with all three off-diagonal entries
zero, both pivot entries vanish, so some nonzero hypothesis is
needed. -/
theorem pivotEntry_ne_of_eq_zero {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (S : Finset (Fin n))
    {u j k : Fin n} (hu : u ∉ S) (hj : j ∉ S) (_hk : k ∉ S)
    (huj : u ≠ j) (_huk : u ≠ k) (_hjk : j ≠ k)
    (hukne : schurEntry A S u k ≠ 0)
    (h0 : pivotEntry A S u j k = 0) : pivotEntry A S j u k ≠ 0 := by
  have hsym : ∀ x y : Fin n, schurEntry A S x y = schurEntry A S y x :=
    fun x y => schurEntry_symm hA S x y
  have huu : schurEntry A S u u ≠ 0 :=
    ne_of_gt (schurEntry_pos hA S hu)
  have hjj : schurEntry A S j j ≠ 0 :=
    ne_of_gt (schurEntry_pos hA S hj)
  by_cases hjk0 : schurEntry A S j k = 0
  · -- `jk = 0` case (paper): the conclusion reduces to `uk ≠ 0`.
    have hkj : schurEntry A S k j = 0 := by
      rw [schurEntry_symm hA S k j]
      exact hjk0
    simp [pivotEntry, hkj, hukne]
  · -- `jk ≠ 0` case: the `2 × 2` minor argument.
    have e0 : schurEntry A S j k
        - schurEntry A S j u * schurEntry A S k u / schurEntry A S u u
          = 0 := h0
    have e1 : schurEntry A S u u * schurEntry A S j k
        = schurEntry A S u j * schurEntry A S u k := by
      have h1 : schurEntry A S j k
          = schurEntry A S j u * schurEntry A S k u / schurEntry A S u u :=
        eq_of_sub_eq_zero e0
      calc schurEntry A S u u * schurEntry A S j k
          = schurEntry A S j u * schurEntry A S k u := by
            rw [h1]
            field_simp
        _ = schurEntry A S u j * schurEntry A S u k := by
            rw [hsym j u, hsym k u]
    intro h1
    have e0' : schurEntry A S u k
        - schurEntry A S u j * schurEntry A S k j / schurEntry A S j j
          = 0 := h1
    have e2 : schurEntry A S j j * schurEntry A S u k
        = schurEntry A S u j * schurEntry A S j k := by
      have h2 : schurEntry A S u k
          = schurEntry A S u j * schurEntry A S k j / schurEntry A S j j :=
        eq_of_sub_eq_zero e0'
      calc schurEntry A S j j * schurEntry A S u k
          = schurEntry A S u j * schurEntry A S k j := by
            rw [h2]
            field_simp
        _ = schurEntry A S u j * schurEntry A S j k := by
            rw [hsym k j]
    have key : schurEntry A S u u * schurEntry A S j j
          * schurEntry A S j k
        = schurEntry A S u j * schurEntry A S u j * schurEntry A S j k := by
      calc schurEntry A S u u * schurEntry A S j j * schurEntry A S j k
          = schurEntry A S j j * (schurEntry A S u u
              * schurEntry A S j k) := by ring
        _ = schurEntry A S j j * (schurEntry A S u j
              * schurEntry A S u k) := by rw [e1]
        _ = schurEntry A S u j * (schurEntry A S j j
              * schurEntry A S u k) := by ring
        _ = schurEntry A S u j * (schurEntry A S u j
              * schurEntry A S j k) := by rw [e2]
        _ = schurEntry A S u j * schurEntry A S u j
              * schurEntry A S j k := by ring
    have hfactor : (schurEntry A S u u * schurEntry A S j j
        - schurEntry A S u j * schurEntry A S u j) ≠ 0 := by
      have h2 := schurEntry_two_mul_sub_pos hA S hu hj huj
      rw [hsym j u] at h2
      exact ne_of_gt h2
    have hz : (schurEntry A S u u * schurEntry A S j j
        - schurEntry A S u j * schurEntry A S u j)
          * schurEntry A S j k = 0 := by
      linear_combination key
    rcases mul_eq_zero.mp hz with hh | hh
    · exact hfactor hh
    · exact hjk0 hh

end CholeskyCancellations

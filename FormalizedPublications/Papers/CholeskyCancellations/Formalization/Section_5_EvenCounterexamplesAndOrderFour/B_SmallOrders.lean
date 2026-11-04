/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Section_5_EvenCounterexamplesAndOrderFour.A_Astar

/-! # Clean orderings at orders three and four (paper Section 5)

Pattern/symbolic comparison helpers, clean orderings for triangles and four-vertex levels, and Conjecture 1 at order three.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as the Section 2 files; concrete matrices are on `Fin 4` and `Fin (2 * m)` with pair/parity read from `Finset` levels and `Fin.val` division as in the paper's `P_k = {2k, 2k+1}` indexing. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


theorem pattern_adj_iff_entry_ne_zero {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {x y : Fin n} (hxy : x ≠ y) :
    (patternGraph A).Adj x y ↔ A x y ≠ 0 := by
  constructor
  · intro h
    have hadj : x ≠ y ∧ (A x y ≠ 0 ∨ A y x ≠ 0) := by
      simpa [patternGraph, SimpleGraph.fromRel_adj] using h
    rcases hadj.2 with h1 | h1
    · exact h1
    · rwa [posDef_apply_comm hA] at h1
  · intro h
    simp only [patternGraph, SimpleGraph.fromRel_adj]
    exact ⟨hxy, Or.inl h⟩



theorem entry_eq_zero_of_not_adj {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {x y : Fin n} (hxy : x ≠ y)
    (h : ¬ (patternGraph A).Adj x y) : A x y = 0 := by
  by_contra hne
  exact h ((pattern_adj_iff_entry_ne_zero hA hxy).mpr hne)



theorem elimStep_adj_iff {G : SimpleGraph (Fin n)} {v x y : Fin n} :
    (elimStep G v).Adj x y
      ↔ x ≠ y ∧ (G.Adj x y ∨ (G.Adj x v ∧ G.Adj y v)) := by
  constructor
  · intro h
    have hadj : x ≠ y ∧ ((G.Adj x y ∨ (G.Adj x v ∧ G.Adj y v))
        ∨ (G.Adj y x ∨ (G.Adj y v ∧ G.Adj x v))) := by
      simpa [elimStep, SimpleGraph.fromRel_adj] using h
    refine ⟨hadj.1, ?_⟩
    rcases hadj.2 with h1 | h1
    · exact h1
    · rcases h1 with h1 | ⟨h1, h2⟩
      · exact Or.inl h1.symm
      · exact Or.inr ⟨h2, h1⟩
  · rintro ⟨hne, h⟩
    simp only [elimStep, SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl h⟩



theorem isOrdering_four {p q j k : Fin 4}
    (hpq : p ≠ q) (hpj : p ≠ j) (hpk : p ≠ k)
    (hqj : q ≠ j) (hqk : q ≠ k) (hjk : j ≠ k) :
    IsOrdering [p, q, j, k] := by
  refine ⟨?_, rfl⟩
  simp [List.nodup_cons, hpq, hpj, hpk, hqj, hqk, hjk]



theorem isOrdering_three {p j k : Fin 3}
    (hpj : p ≠ j) (hpk : p ≠ k) (hjk : j ≠ k) :
    IsOrdering [p, j, k] := by
  refine ⟨?_, rfl⟩
  simp [List.nodup_cons, hpj, hpk, hjk]



theorem exists_two_compl_four {p q : Fin 4} (hpq : p ≠ q) :
    ∃ j k : Fin 4, p ≠ j ∧ p ≠ k ∧ q ≠ j ∧ q ≠ k ∧ j ≠ k
      ∧ ∀ x : Fin 4, x = p ∨ x = q ∨ x = j ∨ x = k := by
  have hcard : (Finset.univ \ {p, q}).card = 2 := by
    simp [Finset.card_sdiff, Fintype.card_fin, Finset.card_pair hpq]
  obtain ⟨j, k, hjk, hset⟩ := Finset.card_eq_two.mp hcard
  have hjmem : j ∈ Finset.univ \ ({p, q} : Finset (Fin 4)) := by
    rw [hset]; simp
  have hkmem : k ∈ Finset.univ \ ({p, q} : Finset (Fin 4)) := by
    rw [hset]; simp
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
    not_or] at hjmem hkmem
  refine ⟨j, k, Ne.symm hjmem.2.1, Ne.symm hkmem.2.1,
    Ne.symm hjmem.2.2, Ne.symm hkmem.2.2, hjk, ?_⟩
  intro x
  by_cases hx : x ∈ ({p, q} : Finset (Fin 4))
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    tauto
  · have hx2 : x ∈ Finset.univ \ ({p, q} : Finset (Fin 4)) := by
      simp [hx]
    rw [hset] at hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
    tauto



theorem exists_adj_of_irreducible {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hIrr : IsIrreducible A) {x : Fin n}
    (hy : ∃ y : Fin n, y ≠ x) :
    ∃ y : Fin n, y ≠ x ∧ (patternGraph A).Adj x y := by
  obtain ⟨y0, hy0⟩ := hy
  have hunion : ({x} : Finset (Fin n)) ∪ (Finset.univ \ {x})
      = Finset.univ := by
    ext z
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    exact iff_of_true (eq_or_ne z x) trivial
  obtain ⟨i, hi, j, hj, hij⟩ := hIrr {x} (Finset.univ \ {x})
    ⟨x, by simp⟩ ⟨y0, by simp [hy0]⟩
    (by simp) hunion
  simp only [Finset.mem_singleton] at hi
  have hxy : x ≠ j := by
    intro h
    rw [h] at hj
    simp at hj
  exact ⟨j, Ne.symm hxy,
    (pattern_adj_iff_entry_ne_zero hA hxy).mpr (hi ▸ hij)⟩



/-- Four-vertex cleanliness from the two second-pivot entries and
the final entry (sufficient conditions at levels `{p}`, `{p,q}`). -/
theorem isClean_four_of {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : A.PosDef)
    {p q j k : Fin 4}
    (hpq : p ≠ q) (hpj : p ≠ j) (hpk : p ≠ k)
    (hqj : q ≠ j) (hqk : q ≠ k) (hjk : j ≠ k)
    (hqj' : (elimStep (patternGraph A) p).Adj q j →
      schurEntry A {p} q j ≠ 0)
    (hqk' : (elimStep (patternGraph A) p).Adj q k →
      schurEntry A {p} q k ≠ 0)
    (hjk' : (elimStep (elimStep (patternGraph A) p) q).Adj j k →
      schurEntry A {p, q} j k ≠ 0) :
    IsCleanOrdering A [p, q, j, k] := by
  have hUniv : ({p, q, j, k} : Finset (Fin 4)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin, Finset.card_eq_four]
    exact ⟨p, q, j, k, hpq, hpj, hpk, hqj, hqk, hjk, rfl⟩
  have hlab : ∀ x : Fin 4, x = p ∨ x = q ∨ x = j ∨ x = k := by
    intro x
    have h : x ∈ ({p, q, j, k} : Finset (Fin 4)) := by rw [hUniv]; simp
    simpa using h
  have hgg1 : gameGraph (patternGraph A) [p]
      = elimStep (patternGraph A) p := by
    simp [gameGraph]
  have hgg2 : gameGraph (patternGraph A) [p, q]
      = elimStep (elimStep (patternGraph A) p) q := by
    simp [gameGraph]
  have hent0 : ∀ x y : Fin 4, prefixList [p, q, j, k] x y = [] →
      PredictedNonzero A [p, q, j, k] x y → A x y ≠ 0 := by
    intro x y hpl hp
    rw [PredictedNonzero, fillGraph_adj_iff, hpl] at hp
    have hadj : (patternGraph A).Adj x y := by
      simpa [gameGraph] using hp
    exact (pattern_adj_iff_entry_ne_zero hA hadj.ne).mp hadj
  have hpl_p : ∀ x : Fin 4, prefixList [p, q, j, k] p x = [] := by
    intro x
    simp [prefixList]
  have hpl_p' : ∀ x : Fin 4, prefixList [p, q, j, k] x p = [] := by
    intro x
    simp [prefixList]
  have hpref_p : ∀ x : Fin 4, prefixSet [p, q, j, k] p x = ∅ := by
    intro x
    simp [prefixSet, hpl_p x]
  have hpref_p' : ∀ x : Fin 4, prefixSet [p, q, j, k] x p = ∅ := by
    intro x
    simp [prefixSet, hpl_p' x]
  have hpl_qj : prefixList [p, q, j, k] q j = [p] := by
    simp [prefixList, hpq, hpj]
  have hpl_qk : prefixList [p, q, j, k] q k = [p] := by
    simp [prefixList, hpq, hpk]
  have hpl_jq : prefixList [p, q, j, k] j q = [p] := by
    simp [prefixList, hpq, hpj]
  have hpl_kq : prefixList [p, q, j, k] k q = [p] := by
    simp [prefixList, hpq, hpk]
  have hpl_jk : prefixList [p, q, j, k] j k = [p, q] := by
    simp [prefixList, hpj, hpk, hqj, hqk]
  have hpl_kj : prefixList [p, q, j, k] k j = [p, q] := by
    simp [prefixList, hpj, hpk, hqj, hqk]
  have hpref_qj : prefixSet [p, q, j, k] q j = {p} := by
    simp [prefixSet, hpl_qj]
  have hpref_qk : prefixSet [p, q, j, k] q k = {p} := by
    simp [prefixSet, hpl_qk]
  have hpref_jq : prefixSet [p, q, j, k] j q = {p} := by
    simp [prefixSet, hpl_jq]
  have hpref_kq : prefixSet [p, q, j, k] k q = {p} := by
    simp [prefixSet, hpl_kq]
  have hpref_jk : prefixSet [p, q, j, k] j k = {p, q} := by
    simp [prefixSet, hpl_jk]
  have hpref_kj : prefixSet [p, q, j, k] k j = {p, q} := by
    simp [prefixSet, hpl_kj]
  have hqj_ne : PredictedNonzero A [p, q, j, k] q j →
      schurEntry A {p} q j ≠ 0 := by
    intro hp
    apply hqj'
    rw [PredictedNonzero, fillGraph_adj_iff, hpl_qj, hgg1] at hp
    exact hp
  have hqk_ne : PredictedNonzero A [p, q, j, k] q k →
      schurEntry A {p} q k ≠ 0 := by
    intro hp
    apply hqk'
    rw [PredictedNonzero, fillGraph_adj_iff, hpl_qk, hgg1] at hp
    exact hp
  have hjk_ne : PredictedNonzero A [p, q, j, k] j k →
      schurEntry A {p, q} j k ≠ 0 := by
    intro hp
    apply hjk'
    rw [PredictedNonzero, fillGraph_adj_iff, hpl_jk, hgg2] at hp
    exact hp
  intro x y hpred
  have hxy : x ≠ y := hpred.ne
  rcases hlab x with hx | hx | hx | hx <;>
    rcases hlab y with hy | hy | hy | hy <;> rw [hx, hy] at hxy hpred ⊢
  · exact absurd rfl hxy
  · rw [hpref_p, schurEntry_empty]
    exact hent0 p q (hpl_p q) hpred
  · rw [hpref_p, schurEntry_empty]
    exact hent0 p j (hpl_p j) hpred
  · rw [hpref_p, schurEntry_empty]
    exact hent0 p k (hpl_p k) hpred
  · rw [hpref_p', schurEntry_empty]
    exact hent0 q p (hpl_p' q) hpred
  · exact absurd rfl hxy
  · rw [hpref_qj]
    exact hqj_ne hpred
  · rw [hpref_qk]
    exact hqk_ne hpred
  · rw [hpref_p', schurEntry_empty]
    exact hent0 j p (hpl_p' j) hpred
  · rw [hpref_jq, schurEntry_symm hA]
    exact hqj_ne hpred.symm
  · exact absurd rfl hxy
  · rw [hpref_jk]
    exact hjk_ne hpred
  · rw [hpref_p', schurEntry_empty]
    exact hent0 k p (hpl_p' k) hpred
  · rw [hpref_kq, schurEntry_symm hA]
    exact hqk_ne hpred.symm
  · rw [hpref_kj, schurEntry_symm hA]
    exact hjk_ne hpred.symm
  · exact absurd rfl hxy



/-- Three-vertex cleanliness from the final entry. -/
theorem isClean_three_of {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.PosDef)
    {p j k : Fin 3}
    (hpj : p ≠ j) (hpk : p ≠ k) (hjk : j ≠ k)
    (hjk' : (elimStep (patternGraph A) p).Adj j k →
      schurEntry A {p} j k ≠ 0) :
    IsCleanOrdering A [p, j, k] := by
  have hUniv : ({p, j, k} : Finset (Fin 3)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin, Finset.card_eq_three]
    exact ⟨p, j, k, hpj, hpk, hjk, rfl⟩
  have hlab : ∀ x : Fin 3, x = p ∨ x = j ∨ x = k := by
    intro x
    have h : x ∈ ({p, j, k} : Finset (Fin 3)) := by rw [hUniv]; simp
    simpa using h
  have hgg1 : gameGraph (patternGraph A) [p]
      = elimStep (patternGraph A) p := by
    simp [gameGraph]
  have hent0 : ∀ x y : Fin 3, prefixList [p, j, k] x y = [] →
      PredictedNonzero A [p, j, k] x y → A x y ≠ 0 := by
    intro x y hpl hp
    rw [PredictedNonzero, fillGraph_adj_iff, hpl] at hp
    have hadj : (patternGraph A).Adj x y := by
      simpa [gameGraph] using hp
    exact (pattern_adj_iff_entry_ne_zero hA hadj.ne).mp hadj
  have hpl_p : ∀ x : Fin 3, prefixList [p, j, k] p x = [] := by
    intro x
    simp [prefixList]
  have hpl_p' : ∀ x : Fin 3, prefixList [p, j, k] x p = [] := by
    intro x
    simp [prefixList]
  have hpref_p : ∀ x : Fin 3, prefixSet [p, j, k] p x = ∅ := by
    intro x
    simp [prefixSet, hpl_p x]
  have hpref_p' : ∀ x : Fin 3, prefixSet [p, j, k] x p = ∅ := by
    intro x
    simp [prefixSet, hpl_p' x]
  have hpl_jk : prefixList [p, j, k] j k = [p] := by
    simp [prefixList, hpj, hpk]
  have hpl_kj : prefixList [p, j, k] k j = [p] := by
    simp [prefixList, hpj, hpk]
  have hpref_jk : prefixSet [p, j, k] j k = {p} := by
    simp [prefixSet, hpl_jk]
  have hpref_kj : prefixSet [p, j, k] k j = {p} := by
    simp [prefixSet, hpl_kj]
  have hjk_ne : PredictedNonzero A [p, j, k] j k →
      schurEntry A {p} j k ≠ 0 := by
    intro hp
    apply hjk'
    rw [PredictedNonzero, fillGraph_adj_iff, hpl_jk, hgg1] at hp
    exact hp
  intro x y hpred
  have hxy : x ≠ y := hpred.ne
  rcases hlab x with hx | hx | hx <;>
    rcases hlab y with hy | hy | hy <;> rw [hx, hy] at hxy hpred ⊢
  · exact absurd rfl hxy
  · rw [hpref_p, schurEntry_empty]
    exact hent0 p j (hpl_p j) hpred
  · rw [hpref_p, schurEntry_empty]
    exact hent0 p k (hpl_p k) hpred
  · rw [hpref_p', schurEntry_empty]
    exact hent0 j p (hpl_p' j) hpred
  · exact absurd rfl hxy
  · rw [hpref_jk]
    exact hjk_ne hpred
  · rw [hpref_p', schurEntry_empty]
    exact hent0 k p (hpl_p' k) hpred
  · rw [hpref_kj, schurEntry_symm hA]
    exact hjk_ne hpred.symm
  · exact absurd rfl hxy



/-- Triangle apex existence at a general level, transferred from
`triangle` through the `3 × 3` Schur submatrix on `{x, y, z}`. -/
theorem level_triangle_not_zeroes {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (S : Finset (Fin n)) {x y z : Fin n}
    (hxS : x ∉ S) (hyS : y ∉ S) (hzS : z ∉ S)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxy' : schurEntry A S x y ≠ 0) (hxz' : schurEntry A S x z ≠ 0)
    (hyz' : schurEntry A S y z ≠ 0) :
    ¬ Zeroes A S x y z ∨ ¬ Zeroes A S y x z
      ∨ ¬ Zeroes A S z x y := by
  set e : Fin 3 → Fin n := ![x, y, z] with he
  have heS : ∀ i : Fin 3, e i ∉ S := by
    intro i
    fin_cases i
    · simpa [he] using hxS
    · simpa [he] using hyS
    · simpa [he] using hzS
  set B : Matrix (Fin 3) (Fin 3) ℝ :=
    fun i j => schurEntry A S (e i) (e j) with hB
  have hBdef : ∀ i j : Fin 3, B i j = schurEntry A S (e i) (e j) :=
    fun i j => rfl
  have hBpos : B.PosDef := by
    have hBeq : B = (schurSet A S).submatrix
        (fun i => (⟨e i, Finset.mem_compl.mpr (heS i)⟩ : Survivors S))
        (fun i => (⟨e i, Finset.mem_compl.mpr (heS i)⟩ : Survivors S)) := by
      ext i j
      simp only [hB, Matrix.submatrix_apply]
      exact schurEntry_eq S (heS i) (heS j)
    rw [hBeq]
    apply Matrix.PosDef.submatrix (schurSet_posDef hA S)
    intro i j hij
    have hval : e i = e j := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hB01 : B 0 1 ≠ 0 := by
    rw [hBdef]
    simpa [he] using hxy'
  have hB21 : B 2 1 ≠ 0 := by
    rw [hBdef]
    have h : schurEntry A S z y ≠ 0 := by
      rw [schurEntry_symm hA]
      exact hyz'
    simpa [he] using h
  have hB20 : B 2 0 ≠ 0 := by
    rw [hBdef]
    have h : schurEntry A S z x ≠ 0 := by
      rw [schurEntry_symm hA]
      exact hxz'
    simpa [he] using h
  obtain ⟨a, _ha, _b, _hb, _hab, hapex, -⟩ :=
    (triangle B hBpos 0 1 2 (by decide) (by decide) (by decide)
      hB01 hB21 hB20).2
  fin_cases a
  · refine Or.inl (fun hz => hapex 1 (by simp) 2 (by simp)
      ⟨by simp, by decide, by decide, by decide, ?_⟩)
    simp only [schurEntry_empty, hBdef]
    simpa [he] using hz.2.2.2.2
  · refine Or.inr (Or.inl (fun hz => hapex 0 (by simp) 2 (by simp)
      ⟨by simp, by decide, by decide, by decide, ?_⟩))
    simp only [schurEntry_empty, hBdef]
    simpa [he] using hz.2.2.2.2
  · refine Or.inr (Or.inr (fun hz => hapex 0 (by simp) 1 (by simp)
      ⟨by simp, by decide, by decide, by decide, ?_⟩))
    simp only [schurEntry_empty, hBdef]
    simpa [he] using hz.2.2.2.2



/-- Clean four-ordering when the three survivors of the first pivot
form a numeric triangle at level `{p}` (paper observation (O2)). -/
theorem exists_clean_four_triangle_level
    {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : A.PosDef) {p x y z : Fin 4}
    (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxy' : schurEntry A {p} x y ≠ 0) (hxz' : schurEntry A {p} x z ≠ 0)
    (hyz' : schurEntry A {p} y z ≠ 0) :
    ∃ σ : List (Fin 4), IsOrdering σ ∧ IsCleanOrdering A σ := by
  have entry_of_not_zeroes : ∀ {u v w : Fin 4},
      u ≠ v → u ≠ w → v ≠ w → p ≠ u → p ≠ v → p ≠ w →
      ¬ Zeroes A {p} u v w → schurEntry A {p, u} v w ≠ 0 := by
    intro u v w huv huw hvw hpu hpv hpw hz hzero
    apply hz
    have huS : u ∉ ({p} : Finset (Fin 4)) := by
      simp only [Finset.mem_singleton]
      exact Ne.symm hpu
    have hvI : v ∉ insert u ({p} : Finset (Fin 4)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm huv, Ne.symm hpv⟩
    have hwI : w ∉ insert u ({p} : Finset (Fin 4)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm huw, Ne.symm hpw⟩
    apply (zeroes_iff_entry_eq_zero A hA huS hvI hwI hvw).mpr
    rwa [Finset.pair_comm] at hzero
  rcases level_triangle_not_zeroes hA {p}
      (by simp only [Finset.mem_singleton]; exact Ne.symm hpx)
      (by simp only [Finset.mem_singleton]; exact Ne.symm hpy)
      (by simp only [Finset.mem_singleton]; exact Ne.symm hpz)
      hxy hxz hyz hxy' hxz' hyz' with hz | hz | hz
  · exact ⟨[p, x, y, z], isOrdering_four hpx hpy hpz hxy hxz hyz,
      isClean_four_of hA hpx hpy hpz hxy hxz hyz
        (fun _ => hxy') (fun _ => hxz')
        (fun _ => entry_of_not_zeroes hxy hxz hyz hpx hpy hpz hz)⟩
  · exact ⟨[p, y, x, z], isOrdering_four hpy hpx hpz (Ne.symm hxy) hyz hxz,
      isClean_four_of hA hpy hpx hpz (Ne.symm hxy) hyz hxz
        (fun _ => by rw [schurEntry_symm hA]; exact hxy')
        (fun _ => hyz')
        (fun _ => entry_of_not_zeroes (Ne.symm hxy) hyz hxz hpy hpx hpz
          hz)⟩
  · exact ⟨[p, z, x, y], isOrdering_four hpz hpx hpy (Ne.symm hxz)
        (Ne.symm hyz) hxy,
      isClean_four_of hA hpz hpx hpy (Ne.symm hxz) (Ne.symm hyz) hxy
        (fun _ => by rw [schurEntry_symm hA]; exact hxz')
        (fun _ => by rw [schurEntry_symm hA]; exact hyz')
        (fun _ => entry_of_not_zeroes (Ne.symm hxz) (Ne.symm hyz) hxy
          hpz hpx hpy hz)⟩



/-- Clean four-ordering when the three survivors of the first pivot
form a numeric path `l1-c-l2` at level `{p}`. -/
theorem exists_clean_four_path_level
    {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : A.PosDef) {p c l1 l2 : Fin 4}
    (hpl1 : p ≠ l1) (hpc : p ≠ c) (hpl2 : p ≠ l2)
    (hl1c : l1 ≠ c) (hl1l2 : l1 ≠ l2) (hcl2 : c ≠ l2)
    (h1 : schurEntry A {p} l1 c ≠ 0) (h2 : schurEntry A {p} l2 c ≠ 0)
    (hz : schurEntry A {p} l1 l2 = 0)
    (hnotpred : ¬ (elimStep (patternGraph A) p).Adj l1 l2) :
    ∃ σ : List (Fin 4), IsOrdering σ ∧ IsCleanOrdering A σ := by
  refine ⟨[p, l1, c, l2], isOrdering_four hpl1 hpc hpl2 hl1c hl1l2 hcl2,
    isClean_four_of hA hpl1 hpc hpl2 hl1c hl1l2 hcl2
      (fun _ => h1) (fun h => absurd h hnotpred) (fun _ => ?_)⟩
  have hzl := (zero_leg A hA {p} l2 c l1
    (by simp only [Finset.mem_singleton]; exact Ne.symm hpl2)
    (by simp only [Finset.mem_singleton]; exact Ne.symm hpc)
    (by simp only [Finset.mem_singleton]; exact Ne.symm hpl1)
    (Ne.symm hcl2) (Ne.symm hl1l2) (Ne.symm hl1c)
    (by rw [schurEntry_symm hA]; exact hz)).1
  rw [Finset.pair_comm, schurEntry_symm hA, hzl]
  exact h2



/-- Singleton Schur entries are unchanged along a zero leg. -/
theorem schurEntry_singleton_of_leg_zero
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {p x y : Fin n}
    (hpx : p ≠ x) (hpy : p ≠ y) (hxy : x ≠ y) (hleg : A x p = 0) :
    schurEntry A {p} x y = A x y := by
  have h1 := (zero_leg A hA ∅ x y p (by simp) (by simp) (by simp) hxy
    (Ne.symm hpx) (Ne.symm hpy)
    (by rw [schurEntry_empty]; exact hleg)).1
  simpa [schurEntry_empty] using h1



/-- Conjecture 1 at order three: every irreducible SPD `3 × 3`
matrix has a clean ordering. -/
theorem exists_clean_three (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.PosDef) (hIrr : IsIrreducible A) :
    ∃ σ : List (Fin 3), IsOrdering σ ∧ IsCleanOrdering A σ := by
  have hcard : (Finset.univ : Finset (Fin 3)).card = 3 := by simp
  obtain ⟨a, b, c, dab, dac, dbc, hset⟩ :=
    Finset.card_eq_three.mp hcard
  have hlab : ∀ x : Fin 3, x = a ∨ x = b ∨ x = c := by
    intro x
    have h : x ∈ ({a, b, c} : Finset (Fin 3)) := by
      rw [← hset]; simp
    simpa using h
  have hexadj : ∀ x : Fin 3, ∃ y, y ≠ x ∧ (patternGraph A).Adj x y := by
    intro x
    apply exists_adj_of_irreducible hA hIrr
    rcases hlab x with rfl | rfl | rfl
    · exact ⟨b, Ne.symm dab⟩
    · exact ⟨a, dab⟩
    · exact ⟨a, dac⟩
  have hd_a : (patternGraph A).Adj a b ∨ (patternGraph A).Adj a c := by
    obtain ⟨y, hy, hadj⟩ := hexadj a
    have hybc : y = b ∨ y = c := by
      rcases hlab y with h | h | h
      · exact absurd h hy
      · exact Or.inl h
      · exact Or.inr h
    rcases hybc with rfl | rfl
    · exact Or.inl hadj
    · exact Or.inr hadj
  have hd_b : (patternGraph A).Adj a b ∨ (patternGraph A).Adj b c := by
    obtain ⟨y, hy, hadj⟩ := hexadj b
    have hyac : y = a ∨ y = c := by
      rcases hlab y with h | h | h
      · exact Or.inl h
      · exact absurd h hy
      · exact Or.inr h
    rcases hyac with rfl | rfl
    · exact Or.inl hadj.symm
    · exact Or.inr hadj
  have hd_c : (patternGraph A).Adj a c ∨ (patternGraph A).Adj b c := by
    obtain ⟨y, hy, hadj⟩ := hexadj c
    have hyab : y = a ∨ y = b := by
      rcases hlab y with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hy
    rcases hyab with rfl | rfl
    · exact Or.inl hadj.symm
    · exact Or.inr hadj.symm
  have entry0 : ∀ {u v w : Fin 3}, u ≠ v → u ≠ w → v ≠ w →
      ¬ Zeroes A ∅ u v w → schurEntry A {u} v w ≠ 0 := by
    intro u v w huv huw hvw hz hz0
    apply hz
    have hvI : v ∉ insert u (∅ : Finset (Fin 3)) := by
      simp [Ne.symm huv]
    have hwI : w ∉ insert u (∅ : Finset (Fin 3)) := by
      simp [Ne.symm huw]
    apply (zeroes_iff_entry_eq_zero A hA (by simp) hvI hwI hvw).mpr
    simpa using hz0
  have hent : ∀ {x y : Fin 3}, x ≠ y → (patternGraph A).Adj x y →
      schurEntry A ∅ x y ≠ 0 := by
    intro x y hxy hadj
    rw [schurEntry_empty]
    exact (pattern_adj_iff_entry_ne_zero hA hxy).mp hadj
  by_cases eab : (patternGraph A).Adj a b <;>
    by_cases eac : (patternGraph A).Adj a c <;>
    by_cases ebc : (patternGraph A).Adj b c
  · -- triangle
    rcases level_triangle_not_zeroes hA ∅ (by simp) (by simp) (by simp)
        dab dac dbc (hent dab eab) (hent dac eac) (hent dbc ebc)
      with hz | hz | hz
    · exact ⟨[a, b, c], isOrdering_three dab dac dbc,
        isClean_three_of hA dab dac dbc
          (fun _ => entry0 dab dac dbc hz)⟩
    · exact ⟨[b, a, c], isOrdering_three (Ne.symm dab) dbc dac,
        isClean_three_of hA (Ne.symm dab) dbc dac
          (fun _ => entry0 (Ne.symm dab) dbc dac hz)⟩
    · exact ⟨[c, a, b], isOrdering_three (Ne.symm dac) (Ne.symm dbc) dab,
        isClean_three_of hA (Ne.symm dac) (Ne.symm dbc) dab
          (fun _ => entry0 (Ne.symm dac) (Ne.symm dbc) dab hz)⟩
  · -- path, center a: σ = [b, a, c]
    refine ⟨[b, a, c], isOrdering_three (Ne.symm dab) dbc dac,
      isClean_three_of hA (Ne.symm dab) dbc dac (fun _ => ?_)⟩
    have hleg : A c b = 0 :=
      entry_eq_zero_of_not_adj hA (Ne.symm dbc) (fun h => ebc h.symm)
    rw [schurEntry_symm hA,
      schurEntry_singleton_of_leg_zero hA dbc (Ne.symm dab)
        (Ne.symm dac) hleg]
    exact (pattern_adj_iff_entry_ne_zero hA (Ne.symm dac)).mp eac.symm
  · -- path, center b: σ = [a, b, c]
    refine ⟨[a, b, c], isOrdering_three dab dac dbc,
      isClean_three_of hA dab dac dbc (fun _ => ?_)⟩
    have hleg : A c a = 0 :=
      entry_eq_zero_of_not_adj hA (Ne.symm dac) (fun h => eac h.symm)
    rw [schurEntry_symm hA,
      schurEntry_singleton_of_leg_zero hA dac dab (Ne.symm dbc) hleg]
    exact (pattern_adj_iff_entry_ne_zero hA (Ne.symm dbc)).mp ebc.symm
  · exact absurd hd_c (by simp [eac, ebc])
  · -- path, center c: σ = [a, c, b]
    refine ⟨[a, c, b], isOrdering_three dac dab (Ne.symm dbc),
      isClean_three_of hA dac dab (Ne.symm dbc) (fun _ => ?_)⟩
    have hleg : A b a = 0 :=
      entry_eq_zero_of_not_adj hA (Ne.symm dab) (fun h => eab h.symm)
    rw [schurEntry_symm hA,
      schurEntry_singleton_of_leg_zero hA dab dac dbc hleg]
    exact (pattern_adj_iff_entry_ne_zero hA dbc).mp ebc
  · exact absurd hd_b (by simp [eab, ebc])
  · exact absurd hd_a (by simp [eab, eac])
  · exact absurd hd_a (by simp [eab, eac])

end CholeskyCancellations

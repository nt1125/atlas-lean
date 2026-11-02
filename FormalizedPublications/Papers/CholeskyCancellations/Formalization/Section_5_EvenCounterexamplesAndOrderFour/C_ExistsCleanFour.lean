/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Section_5_EvenCounterexamplesAndOrderFour.B_SmallOrders

/-! # Conjecture 1 at order four (paper Section 5)

Every irreducible SPD `4 × 4` matrix has a clean ordering; Conjecture 1 holds at every order `≤ 4` (paper Theorem 5.2). Split from `Counterexamples.lean`.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as `Defs.lean`; concrete matrices are on `Fin 4` and `Fin (2 * m)` with pair/parity read from `Finset` levels and `Fin.val` division as in the paper's `P_k = {2k, 2k+1}` indexing. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- Conjecture 1 at order four. -/
theorem exists_clean_four (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : A.PosDef) (hIrr : IsIrreducible A) :
    ∃ σ : List (Fin 4), IsOrdering σ ∧ IsCleanOrdering A σ := by
  have hexadj : ∀ x : Fin 4, ∃ y, y ≠ x ∧ (patternGraph A).Adj x y := by
    intro x
    apply exists_adj_of_irreducible hA hIrr
    by_contra h
    push Not at h
    have h01 : (0 : Fin 4) = (1 : Fin 4) := (h 0).trans (h 1).symm
    exact (by decide : (0 : Fin 4) ≠ 1) h01
  have notpred_of : ∀ {p x y : Fin 4},
      ¬ (patternGraph A).Adj x y →
      (¬ (patternGraph A).Adj x p ∨ ¬ (patternGraph A).Adj y p) →
      ¬ (elimStep (patternGraph A) p).Adj x y := by
    intro p x y h1 h2 h
    rw [elimStep_adj_iff] at h
    rcases h.2 with h3 | ⟨h3, h4⟩
    · exact h1 h3
    · rcases h2 with h2 | h2
      · exact h2 h3
      · exact h2 h4
  by_cases hLeaf : ∃ p w : Fin 4, p ≠ w ∧ (patternGraph A).Adj p w
      ∧ ∀ y : Fin 4, y ≠ p → (patternGraph A).Adj p y → y = w
  · obtain ⟨p, w, hpw, _hpwAdj, hleaf⟩ := hLeaf
    obtain ⟨j, k, hpj, hpk, hwj, hwk, hjk, hlab⟩ :=
      exists_two_compl_four hpw
    have hnpj : ¬ (patternGraph A).Adj p j :=
      fun h => (Ne.symm hwj) (hleaf j (Ne.symm hpj) h)
    have hnpk : ¬ (patternGraph A).Adj p k :=
      fun h => (Ne.symm hwk) (hleaf k (Ne.symm hpk) h)
    have hS1 : ∀ {x y : Fin 4}, p ≠ x → p ≠ y → x ≠ y →
        schurEntry A {p} x y = A x y := by
      intro x y hpx hpy hxy
      by_cases hxw : x = w
      · have hyw : y ≠ w := fun h => hxy (hxw.trans h.symm)
        have hleg : A y p = 0 :=
          entry_eq_zero_of_not_adj hA (Ne.symm hpy)
            (fun hadj => hyw (hleaf y (Ne.symm hpy) hadj.symm))
        rw [schurEntry_symm hA,
          schurEntry_singleton_of_leg_zero hA hpy hpx (Ne.symm hxy) hleg,
          posDef_apply_comm hA]
      · have hleg : A x p = 0 :=
          entry_eq_zero_of_not_adj hA (Ne.symm hpx)
            (fun hadj => hxw (hleaf x (Ne.symm hpx) hadj.symm))
        exact schurEntry_singleton_of_leg_zero hA hpx hpy hxy hleg
    have hdj : (patternGraph A).Adj w j ∨ (patternGraph A).Adj j k := by
      obtain ⟨y, hyj, hadj⟩ := hexadj j
      have hywk : y = w ∨ y = k := by
        rcases hlab y with h | h | h | h
        · subst h
          exact (hnpj hadj.symm).elim
        · exact Or.inl h
        · exact absurd h hyj
        · exact Or.inr h
      rcases hywk with rfl | rfl
      · exact Or.inl hadj.symm
      · exact Or.inr hadj
    have hdk : (patternGraph A).Adj w k ∨ (patternGraph A).Adj j k := by
      obtain ⟨y, hyk, hadj⟩ := hexadj k
      have hywj : y = w ∨ y = j := by
        rcases hlab y with h | h | h | h
        · subst h
          exact (hnpk hadj.symm).elim
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hyk
      rcases hywj with rfl | rfl
      · exact Or.inl hadj.symm
      · exact Or.inr hadj.symm
    by_cases ewj : (patternGraph A).Adj w j <;>
      by_cases ewk : (patternGraph A).Adj w k <;>
      by_cases ejk : (patternGraph A).Adj j k
    · apply exists_clean_four_triangle_level hA hpw hpj hpk hwj hwk hjk
      · rw [hS1 hpw hpj hwj]
        exact (pattern_adj_iff_entry_ne_zero hA hwj).mp ewj
      · rw [hS1 hpw hpk hwk]
        exact (pattern_adj_iff_entry_ne_zero hA hwk).mp ewk
      · rw [hS1 hpj hpk hjk]
        exact (pattern_adj_iff_entry_ne_zero hA hjk).mp ejk
    · apply exists_clean_four_path_level hA hpj hpw hpk (Ne.symm hwj)
        hjk hwk
      · rw [hS1 hpj hpw (Ne.symm hwj)]
        exact (pattern_adj_iff_entry_ne_zero hA (Ne.symm hwj)).mp ewj.symm
      · rw [hS1 hpk hpw (Ne.symm hwk)]
        exact (pattern_adj_iff_entry_ne_zero hA (Ne.symm hwk)).mp ewk.symm
      · rw [hS1 hpj hpk hjk]
        exact entry_eq_zero_of_not_adj hA hjk ejk
      · exact notpred_of ejk (Or.inl (fun h => hnpj h.symm))
    · apply exists_clean_four_path_level hA hpw hpj hpk hwj hwk hjk
      · rw [hS1 hpw hpj hwj]
        exact (pattern_adj_iff_entry_ne_zero hA hwj).mp ewj
      · rw [hS1 hpk hpj (Ne.symm hjk)]
        exact (pattern_adj_iff_entry_ne_zero hA (Ne.symm hjk)).mp ejk.symm
      · rw [hS1 hpw hpk hwk]
        exact entry_eq_zero_of_not_adj hA hwk ewk
      · exact notpred_of ewk (Or.inr (fun h => hnpk h.symm))
    · exact absurd hdk (by simp [ewk, ejk])
    · apply exists_clean_four_path_level hA hpw hpk hpj hwk hwj
        (Ne.symm hjk)
      · rw [hS1 hpw hpk hwk]
        exact (pattern_adj_iff_entry_ne_zero hA hwk).mp ewk
      · rw [hS1 hpj hpk hjk]
        exact (pattern_adj_iff_entry_ne_zero hA hjk).mp ejk
      · rw [hS1 hpw hpj hwj]
        exact entry_eq_zero_of_not_adj hA hwj ewj
      · exact notpred_of ewj (Or.inr (fun h => hnpj h.symm))
    · exact absurd hdj (by simp [ewj, ejk])
    · -- disconnected 2+2 split {p, w} | {j, k}
      have hzpj : A p j = 0 := entry_eq_zero_of_not_adj hA hpj hnpj
      have hzpk : A p k = 0 := entry_eq_zero_of_not_adj hA hpk hnpk
      have hzwj : A w j = 0 := entry_eq_zero_of_not_adj hA hwj ewj
      have hzwk : A w k = 0 := entry_eq_zero_of_not_adj hA hwk ewk
      have hunion : ({p, w} : Finset (Fin 4)) ∪ {j, k} = Finset.univ := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_univ, iff_true]
        have hx := hlab x
        tauto
      obtain ⟨i, hi, i2, hi2, he⟩ := hIrr {p, w} {j, k}
        ⟨p, by simp⟩ ⟨j, by simp⟩
        (by simp [Finset.disjoint_iff_ne, hpj, hpk, hwj, hwk]) hunion
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hi2
      rcases hi with rfl | rfl <;> rcases hi2 with rfl | rfl
      · exact (he hzpj).elim
      · exact (he hzpk).elim
      · exact (he hzwj).elim
      · exact (he hzwk).elim
    · exact absurd hdj (by simp [ewj, ejk])
  · by_cases hSimp : ∃ p j k : Fin 4, p ≠ j ∧ p ≠ k ∧ j ≠ k ∧
        (patternGraph A).Adj p j ∧ (patternGraph A).Adj p k ∧
        (patternGraph A).Adj j k ∧
        ∀ y : Fin 4, y ≠ p → (patternGraph A).Adj p y → y = j ∨ y = k
    · obtain ⟨p, j, k, hpj, hpk, hjk, _hpja, _hpka, _hjka, hsimp⟩ :=
        hSimp
      have hcard3 : ({p, j, k} : Finset (Fin 4)).card = 3 :=
        Finset.card_eq_three.mpr ⟨p, j, k, hpj, hpk, hjk, rfl⟩
      have hcard1 : (Finset.univ \ {p, j, k}).card = 1 := by
        simp [Finset.card_sdiff, Fintype.card_fin, hcard3]
      obtain ⟨w, hwset⟩ := Finset.card_eq_one.mp hcard1
      have hwmem : w ∈ Finset.univ \ ({p, j, k} : Finset (Fin 4)) := by
        rw [hwset]; simp
      simp only [Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton, not_or] at hwmem
      have hwp : w ≠ p := hwmem.2.1
      have hwj : w ≠ j := hwmem.2.2.1
      have hwk : w ≠ k := hwmem.2.2.2
      have hpw : p ≠ w := Ne.symm hwp
      have hlab : ∀ x : Fin 4, x = p ∨ x = j ∨ x = k ∨ x = w := by
        intro x
        by_cases hx : x ∈ ({p, j, k} : Finset (Fin 4))
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          tauto
        · have hx2 : x ∈ Finset.univ \ ({p, j, k} : Finset (Fin 4)) := by
            simp [hx]
          rw [hwset] at hx2
          simp only [Finset.mem_singleton] at hx2
          exact Or.inr (Or.inr (Or.inr hx2))
      have hnpw : ¬ (patternGraph A).Adj p w := by
        intro h
        rcases hsimp w hwp h with h | h
        · exact hwj h
        · exact hwk h
      have hadj_wj : (patternGraph A).Adj w j := by
        by_contra hnot
        apply hLeaf
        obtain ⟨y, hyw, hadj⟩ := hexadj w
        have hyk : y = k := by
          rcases hlab y with h | h | h | h
          · subst h
            exact (hnpw hadj.symm).elim
          · subst h
            exact (hnot hadj).elim
          · exact h
          · exact absurd h hyw
        have hadj' : (patternGraph A).Adj w k := by
          rw [hyk] at hadj
          exact hadj
        refine ⟨w, k, hwk, hadj', ?_⟩
        intro y2 hy2 hadj2
        rcases hlab y2 with h | h | h | h
        · subst h
          exact (hnpw hadj2.symm).elim
        · subst h
          exact (hnot hadj2).elim
        · exact h
        · exact absurd h hy2
      have hadj_wk : (patternGraph A).Adj w k := by
        by_contra hnot
        apply hLeaf
        obtain ⟨y, hyw, hadj⟩ := hexadj w
        have hyj : y = j := by
          rcases hlab y with h | h | h | h
          · subst h
            exact (hnpw hadj.symm).elim
          · exact h
          · subst h
            exact (hnot hadj).elim
          · exact absurd h hyw
        have hadj' : (patternGraph A).Adj w j := by
          rw [hyj] at hadj
          exact hadj
        refine ⟨w, j, hwj, hadj', ?_⟩
        intro y2 hy2 hadj2
        rcases hlab y2 with h | h | h | h
        · subst h
          exact (hnpw hadj2.symm).elim
        · exact h
        · subst h
          exact (hnot hadj2).elim
        · exact absurd h hy2
      have hleg_wp : A w p = 0 :=
        entry_eq_zero_of_not_adj hA hwp (fun h => hnpw h.symm)
      have hSwj : schurEntry A {p} w j ≠ 0 := by
        rw [schurEntry_singleton_of_leg_zero hA hpw hpj hwj hleg_wp]
        exact (pattern_adj_iff_entry_ne_zero hA hwj).mp hadj_wj
      have hSjw : schurEntry A {p} j w ≠ 0 := by
        rw [schurEntry_symm hA]
        exact hSwj
      have hSwk : schurEntry A {p} w k ≠ 0 := by
        rw [schurEntry_singleton_of_leg_zero hA hpw hpk hwk hleg_wp]
        exact (pattern_adj_iff_entry_ne_zero hA hwk).mp hadj_wk
      have hSkw : schurEntry A {p} k w ≠ 0 := by
        rw [schurEntry_symm hA]
        exact hSwk
      by_cases hz : schurEntry A {p} j k = 0
      · have huniv : IsUniversalAt A {p} w := by
          refine ⟨?_, ?_⟩
          · simp only [Finset.mem_singleton]
            exact hwp
          · intro y hy hyw
            have hyp : y ≠ p := by
              simp only [Finset.mem_singleton] at hy
              exact hy
            rcases hlab y with h | h | h | h
            · exact absurd h hyp
            · subst h
              exact hSwj
            · subst h
              exact hSwk
            · exact absurd h hyw
        have hjI : j ∉ insert w ({p} : Finset (Fin 4)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm hwj, Ne.symm hpj⟩
        have hkI : k ∉ insert w ({p} : Finset (Fin 4)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm hwk, Ne.symm hpk⟩
        have hfin := (universal_pivot_refill A hA {p} w huniv).1
          j k hjI hkI hjk hz
        exact ⟨[p, w, j, k], isOrdering_four hpw hpj hpk hwj hwk hjk,
          isClean_four_of hA hpw hpj hpk hwj hwk hjk
            (fun _ => hSwj) (fun _ => hSwk)
            (fun _ => by rw [Finset.pair_comm]; exact hfin.2)⟩
      · exact exists_clean_four_triangle_level hA hpj hpk hpw hjk
          (Ne.symm hwj) (Ne.symm hwk) hz hSjw hSkw
    · by_cases hComplete : ∀ x y : Fin 4, x ≠ y →
          (patternGraph A).Adj x y
      · -- `K_4`: max edge first, then refill or triangle.
        set s : Finset (Fin 4 × Fin 4) :=
          (Finset.univ ×ˢ Finset.univ).filter
            (fun pq => pq.1 ≠ pq.2) with hs
        have hsne : s.Nonempty := ⟨(0, 1), by simp [hs]⟩
        obtain ⟨⟨p, q⟩, hpqmem, hmax⟩ := Finset.exists_max_image s
          (fun pq => logMag A ∅ pq.1 pq.2) hsne
        have hpq : p ≠ q := (Finset.mem_filter.mp hpqmem).2
        have hmax' : ∀ i j : Fin 4, i ≠ j →
            logMag A ∅ i j ≤ logMag A ∅ p q := by
          intro i j hij
          exact hmax (i, j) (by simp [hs, hij])
        obtain ⟨j, k, hpj, hpk, hqj, hqk, hjk, hlab⟩ :=
          exists_two_compl_four hpq
        have hnc := (max_edge A hA
          (fun i j hij => (pattern_adj_iff_entry_ne_zero hA hij).mp
            (hComplete i j hij)) p q hpq hmax').1
        have entry_q_of : ∀ {x : Fin 4}, x ≠ p → q ≠ x →
            schurEntry A {p} q x ≠ 0 := by
          intro x hxp hqx hz0
          apply hnc
          refine ⟨x, Or.inl ?_⟩
          have hqI : q ∉ insert p (∅ : Finset (Fin 4)) := by
            simp [Ne.symm hpq]
          have hxI : x ∉ insert p (∅ : Finset (Fin 4)) := by
            simp [hxp]
          apply (zeroes_iff_entry_eq_zero A hA (by simp) hqI hxI
            hqx).mpr
          simpa using hz0
        have hqj1 : schurEntry A {p} q j ≠ 0 :=
          entry_q_of (Ne.symm hpj) hqj
        have hqk1 : schurEntry A {p} q k ≠ 0 :=
          entry_q_of (Ne.symm hpk) hqk
        by_cases hz : schurEntry A {p} j k = 0
        · have huniv : IsUniversalAt A {p} q := by
            refine ⟨?_, ?_⟩
            · simp only [Finset.mem_singleton]
              exact Ne.symm hpq
            · intro y hy hyq
              have hyp : y ≠ p := by
                simp only [Finset.mem_singleton] at hy
                exact hy
              rcases hlab y with h | h | h | h
              · exact absurd h hyp
              · exact absurd h hyq
              · subst h
                exact hqj1
              · subst h
                exact hqk1
          have hjI : j ∉ insert q ({p} : Finset (Fin 4)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨Ne.symm hqj, Ne.symm hpj⟩
          have hkI : k ∉ insert q ({p} : Finset (Fin 4)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨Ne.symm hqk, Ne.symm hpk⟩
          have hfin := (universal_pivot_refill A hA {p} q huniv).1
            j k hjI hkI hjk hz
          exact ⟨[p, q, j, k], isOrdering_four hpq hpj hpk hqj hqk hjk,
            isClean_four_of hA hpq hpj hpk hqj hqk hjk
              (fun _ => hqj1) (fun _ => hqk1)
              (fun _ => by rw [Finset.pair_comm]; exact hfin.2)⟩
        · exact exists_clean_four_triangle_level hA hpq hpj hpk hqj hqk
            hjk hqj1 hqk1 hz
      · -- `C_4`: pivot a vertex, fresh fill creates the triangle.
        push Not at hComplete
        obtain ⟨p, w, hpw, hnpw⟩ := hComplete
        obtain ⟨j, k, hpj, hpk, hwj, hwk, hjk, hlab⟩ :=
          exists_two_compl_four hpw
        have not_leaf_adj : ∀ {u o t1 t2 : Fin 4},
            u ≠ o → u ≠ t1 → u ≠ t2 → o ≠ t1 → o ≠ t2 → t1 ≠ t2 →
            ¬ (patternGraph A).Adj u o →
            (∀ x : Fin 4, x = u ∨ x = o ∨ x = t1 ∨ x = t2) →
            (patternGraph A).Adj u t1 := by
          intro u o t1 t2 huo hut1 hut2 _hot1 _hot2 _ht12 hnuo hlab2
          by_contra hnot
          apply hLeaf
          obtain ⟨y, hyu, hadj⟩ := hexadj u
          have hy : y = t2 := by
            rcases hlab2 y with h | h | h | h
            · exact absurd h hyu
            · subst h
              exact (hnuo hadj).elim
            · subst h
              exact (hnot hadj).elim
            · exact h
          have hadj' : (patternGraph A).Adj u t2 := by
            rw [hy] at hadj
            exact hadj
          refine ⟨u, t2, hut2, hadj', ?_⟩
          intro y2 hy2 hadj2
          rcases hlab2 y2 with h | h | h | h
          · exact absurd h hy2
          · subst h
            exact (hnuo hadj2).elim
          · subst h
            exact (hnot hadj2).elim
          · exact h
        have hlab_pj : ∀ x : Fin 4, x = p ∨ x = w ∨ x = k ∨ x = j := by
          intro x
          rcases hlab x with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inr (Or.inr (Or.inl h))
        have hlab_wj : ∀ x : Fin 4, x = w ∨ x = p ∨ x = j ∨ x = k := by
          intro x
          rcases hlab x with h | h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
        have hlab_wk : ∀ x : Fin 4, x = w ∨ x = p ∨ x = k ∨ x = j := by
          intro x
          rcases hlab x with h | h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inr (Or.inr (Or.inl h))
        have hnw : ¬ (patternGraph A).Adj w p :=
          fun h => hnpw h.symm
        have hpjA : (patternGraph A).Adj p j :=
          not_leaf_adj hpw hpj hpk hwj hwk hjk hnpw hlab
        have hpkA : (patternGraph A).Adj p k :=
          not_leaf_adj hpw hpk hpj hwk hwj (Ne.symm hjk) hnpw hlab_pj
        have hwjA : (patternGraph A).Adj w j :=
          not_leaf_adj (Ne.symm hpw) hwj hwk hpj hpk hjk hnw hlab_wj
        have hwkA : (patternGraph A).Adj w k :=
          not_leaf_adj (Ne.symm hpw) hwk hwj hpk hpj (Ne.symm hjk) hnw
            hlab_wk
        have hnjk : ¬ (patternGraph A).Adj j k := by
          intro hjkA
          apply hSimp
          refine ⟨p, j, k, hpj, hpk, hjk, hpjA, hpkA, hjkA, ?_⟩
          intro y hyp hadj
          rcases hlab y with h | h | h | h
          · exact absurd h hyp
          · subst h
            exact (hnpw hadj).elim
          · exact Or.inl h
          · exact Or.inr h
        have hjI : j ∉ insert p (∅ : Finset (Fin 4)) := by
          simp [Ne.symm hpj]
        have hkI : k ∉ insert p (∅ : Finset (Fin 4)) := by
          simp [Ne.symm hpk]
        have hf := fresh_fill A hA [] ∅ ⟨by simp, by simp⟩ p j k
          (by simp) hjI hkI hjk
          (by simpa [gameGraph] using hpjA.symm)
          (by simpa [gameGraph] using hpkA.symm)
          (by simpa [gameGraph] using hnjk)
        have hSjk : schurEntry A {p} j k ≠ 0 := by
          have hlegj : schurEntry A ∅ j p ≠ 0 := by
            rw [schurEntry_empty]
            exact (pattern_adj_iff_entry_ne_zero hA
              (Ne.symm hpj)).mp hpjA.symm
          have hlegk : schurEntry A ∅ k p ≠ 0 := by
            rw [schurEntry_empty]
            exact (pattern_adj_iff_entry_ne_zero hA
              (Ne.symm hpk)).mp hpkA.symm
          have hfin := hf.2.2 hlegj hlegk
          simpa using hfin
        have hleg_wp : A w p = 0 :=
          entry_eq_zero_of_not_adj hA (Ne.symm hpw) hnw
        have hSjw : schurEntry A {p} j w ≠ 0 := by
          rw [schurEntry_symm hA,
            schurEntry_singleton_of_leg_zero hA hpw hpj hwj hleg_wp]
          exact (pattern_adj_iff_entry_ne_zero hA hwj).mp hwjA
        have hSkw : schurEntry A {p} k w ≠ 0 := by
          rw [schurEntry_symm hA,
            schurEntry_singleton_of_leg_zero hA hpw hpk hwk hleg_wp]
          exact (pattern_adj_iff_entry_ne_zero hA hwk).mp hwkA
        exact exists_clean_four_triangle_level hA hpj hpk hpw hjk
          (Ne.symm hwj) (Ne.symm hwk) hSjk hSjw hSkw



/-- `clean_of_order_le_four`: Conjecture 1 holds at every
order at most 4 (paper Theorem 5.2, `thm:leq4`). -/
theorem clean_of_order_le_four : ∀ {n : ℕ}, n ≤ 4 →
    ∀ A : Matrix (Fin n) (Fin n) ℝ,
    A.PosDef → IsIrreducible A →
      ∃ σ : List (Fin n), IsOrdering σ ∧ IsCleanOrdering A σ := by
  intro n hn A hA hIrr
  interval_cases n
  · exact ⟨[], by simp [IsOrdering],
      by intro j k _; exact absurd j.2 (Nat.not_lt_zero _)⟩
  · refine ⟨[0], by simp [IsOrdering], ?_⟩
    intro j k hpred
    have hjk : j = k := by
      apply Fin.ext
      have hj := j.2
      have hk := k.2
      omega
    exact absurd hjk hpred.ne
  · have hcard : (Finset.univ : Finset (Fin 2)).card = 2 := by simp
    obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hcard
    have hlab : ∀ x : Fin 2, x = a ∨ x = b := by
      intro x
      have h : x ∈ ({a, b} : Finset (Fin 2)) := by
        rw [← hset]; simp
      simpa using h
    refine ⟨[a, b], by simp [IsOrdering, List.nodup_cons, hab], ?_⟩
    have hent : ∀ u v : Fin 2, prefixList [a, b] u v = [] →
        PredictedNonzero A [a, b] u v → A u v ≠ 0 := by
      intro u v hpl hp
      rw [PredictedNonzero, fillGraph_adj_iff, hpl] at hp
      have hadj : (patternGraph A).Adj u v := by
        simpa [gameGraph] using hp
      exact (pattern_adj_iff_entry_ne_zero hA hadj.ne).mp hadj
    have hpref_ab : prefixSet [a, b] a b = ∅ := by
      simp [prefixSet, prefixList]
    have hpref_ba : prefixSet [a, b] b a = ∅ := by
      simp [prefixSet, prefixList]
    have hpl_ab : prefixList [a, b] a b = [] := by simp [prefixList]
    have hpl_ba : prefixList [a, b] b a = [] := by simp [prefixList]
    intro x y hpred
    have hxy : x ≠ y := hpred.ne
    rcases hlab x with hx | hx <;> rcases hlab y with hy | hy <;>
      rw [hx, hy] at hxy hpred ⊢
    · exact absurd rfl hxy
    · rw [hpref_ab, schurEntry_empty]
      exact hent a b hpl_ab hpred
    · rw [hpref_ba, schurEntry_empty]
      exact hent b a hpl_ba hpred
    · exact absurd rfl hxy
  · exact exists_clean_three A hA hIrr
  · exact exists_clean_four A hA hIrr

end CholeskyCancellations

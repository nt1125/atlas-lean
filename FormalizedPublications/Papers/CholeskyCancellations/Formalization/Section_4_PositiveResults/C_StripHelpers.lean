/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.TakeWhile
import Section_4_PositiveResults.B_StripMachinery

/-! # Strip helpers (paper Section 4)

Distance-one/two membership lemmas, game-graph append facts, Schur-entry computations, and the small strip state lemmas. The Exchange Lemma and its `2 × 2` minor lemma are in Section 3 (`C_ExchangeLemma.lean`).
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as the Section 2 files; graph classes are predicates on `SimpleGraph (Fin n)` patterns and cleanliness is quantified per SPD realization through `PatternAdmitsPerMatrixCleanOrdering`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}



theorem distOneIn_mem {l : List (Fin n)} {x y : Fin n}
    (h : DistOneIn l x y) : x ∈ l ∧ y ∈ l := by
  rcases h with ⟨l₁, l₂, rfl⟩ | ⟨l₁, l₂, rfl⟩ <;> simp



theorem distTwoIn_mem {l : List (Fin n)} {x y : Fin n}
    (h : DistTwoIn l x y) : x ∈ l ∧ y ∈ l := by
  rcases h with ⟨l₁, l₂, z, rfl⟩ | ⟨l₁, l₂, z, rfl⟩ <;> simp



theorem distOneIn_cons_iff {z x y : Fin n} {l : List (Fin n)} :
    DistOneIn (z :: l) x y ↔
      (x = z ∧ ∃ w rest, l = w :: rest ∧ y = w)
        ∨ (y = z ∧ ∃ w rest, l = w :: rest ∧ x = w)
        ∨ DistOneIn l x y := by
  constructor
  · rintro (⟨l₁, l₂, hl⟩ | ⟨l₁, l₂, hl⟩)
    · cases l₁ with
      | nil =>
          simp only [List.nil_append] at hl
          obtain ⟨rfl, rfl⟩ := List.cons.inj hl
          exact Or.inl ⟨rfl, y, l₂, rfl, rfl⟩
      | cons w l₁ =>
          have h2 : z :: l = w :: (l₁ ++ x :: y :: l₂) := by
            simpa using hl
          exact Or.inr (Or.inr (Or.inl ⟨l₁, l₂, (List.cons.inj h2).2⟩))
    · cases l₁ with
      | nil =>
          simp only [List.nil_append] at hl
          obtain ⟨rfl, rfl⟩ := List.cons.inj hl
          exact Or.inr (Or.inl ⟨rfl, x, l₂, rfl, rfl⟩)
      | cons w l₁ =>
          have h2 : z :: l = w :: (l₁ ++ y :: x :: l₂) := by
            simpa using hl
          exact Or.inr (Or.inr (Or.inr ⟨l₁, l₂, (List.cons.inj h2).2⟩))
  · rintro (⟨rfl, w, rest, rfl, rfl⟩ | ⟨rfl, w, rest, rfl, rfl⟩ |
      (⟨l₁, l₂, hl⟩ | ⟨l₁, l₂, hl⟩))
    · exact Or.inl ⟨[], rest, rfl⟩
    · exact Or.inr ⟨[], rest, rfl⟩
    · exact Or.inl ⟨z :: l₁, l₂, by simp [hl]⟩
    · exact Or.inr ⟨z :: l₁, l₂, by simp [hl]⟩



theorem distTwoIn_cons_iff {z x y : Fin n} {l : List (Fin n)} :
    DistTwoIn (z :: l) x y ↔
      (x = z ∧ ∃ a b rest, l = a :: b :: rest ∧ y = b)
        ∨ (y = z ∧ ∃ a b rest, l = a :: b :: rest ∧ x = b)
        ∨ DistTwoIn l x y := by
  constructor
  · rintro (⟨l₁, l₂, m, hl⟩ | ⟨l₁, l₂, m, hl⟩)
    · cases l₁ with
      | nil =>
          simp only [List.nil_append] at hl
          obtain ⟨rfl, rfl⟩ := List.cons.inj hl
          exact Or.inl ⟨rfl, m, y, l₂, rfl, rfl⟩
      | cons w l₁ =>
          have h2 : z :: l = w :: (l₁ ++ x :: m :: y :: l₂) := by
            simpa using hl
          exact Or.inr (Or.inr (Or.inl ⟨l₁, l₂, m, (List.cons.inj h2).2⟩))
    · cases l₁ with
      | nil =>
          simp only [List.nil_append] at hl
          obtain ⟨rfl, rfl⟩ := List.cons.inj hl
          exact Or.inr (Or.inl ⟨rfl, m, x, l₂, rfl, rfl⟩)
      | cons w l₁ =>
          have h2 : z :: l = w :: (l₁ ++ y :: m :: x :: l₂) := by
            simpa using hl
          exact Or.inr (Or.inr (Or.inr ⟨l₁, l₂, m, (List.cons.inj h2).2⟩))
  · rintro (⟨rfl, a, b, rest, rfl, rfl⟩ | ⟨rfl, a, b, rest, rfl, rfl⟩ |
      (⟨l₁, l₂, m, hl⟩ | ⟨l₁, l₂, m, hl⟩))
    · exact Or.inl ⟨[], rest, a, rfl⟩
    · exact Or.inr ⟨[], rest, a, rfl⟩
    · exact Or.inl ⟨z :: l₁, l₂, m, by simp [hl]⟩
    · exact Or.inr ⟨z :: l₁, l₂, m, by simp [hl]⟩



/-- The distance-1 partner of the head of a duplicate-free list is
the second vertex. -/
theorem distOne_head {s₁ s₂ : Fin n} {rest : List (Fin n)}
    (hnd : (s₁ :: s₂ :: rest).Nodup) {y : Fin n} :
    DistOneIn (s₁ :: s₂ :: rest) s₁ y → y = s₂ := by
  have hnot : s₁ ∉ s₂ :: rest := (List.nodup_cons.mp hnd).1
  intro h
  rw [distOneIn_cons_iff] at h
  rcases h with ⟨-, w, r, hl, rfl⟩ | ⟨rfl, w, r, hl, hw⟩ | h
  · exact (List.cons.inj hl).1.symm
  · exact hw.trans (List.cons.inj hl).1.symm
  · exact absurd (distOneIn_mem h).1 hnot



/-- The distance-2 partner of the head of a duplicate-free list is
the third vertex. -/
theorem distTwo_head {s₁ s₂ s₃ : Fin n} {rest : List (Fin n)}
    (hnd : (s₁ :: s₂ :: s₃ :: rest).Nodup) {y : Fin n} :
    DistTwoIn (s₁ :: s₂ :: s₃ :: rest) s₁ y → y = s₃ := by
  have hnot : s₁ ∉ s₂ :: s₃ :: rest := (List.nodup_cons.mp hnd).1
  intro h
  rw [distTwoIn_cons_iff] at h
  rcases h with ⟨-, a, b, r, hl, rfl⟩ | ⟨rfl, a, b, r, hl, hw⟩ | h
  · exact (List.cons.inj (List.cons.inj hl).2).1.symm
  · exact hw.trans (List.cons.inj (List.cons.inj hl).2).1.symm
  · exact absurd (distTwoIn_mem h).1 hnot



/-- The distance-1/2 partners of the second vertex of a
duplicate-free strip list are exactly its two neighbours and the
fourth vertex. -/
theorem dist_second {s₁ s₂ s₃ s₄ : Fin n} {rest : List (Fin n)}
    (hnd : (s₁ :: s₂ :: s₃ :: s₄ :: rest).Nodup) {y : Fin n} :
    DistOneIn (s₁ :: s₂ :: s₃ :: s₄ :: rest) s₂ y
      ∨ DistTwoIn (s₁ :: s₂ :: s₃ :: s₄ :: rest) s₂ y
        → y = s₁ ∨ y = s₃ ∨ y = s₄ := by
  have hnd' : (s₂ :: s₃ :: s₄ :: rest).Nodup := (List.nodup_cons.mp hnd).2
  have h21 : s₂ ≠ s₁ := by
    have hnot := (List.nodup_cons.mp hnd).1
    intro hh
    exact hnot (hh ▸ by simp)
  have h23 : s₂ ≠ s₃ := by
    have hnot := (List.nodup_cons.mp hnd').1
    intro hh
    exact hnot (hh ▸ by simp)
  rintro (h | h)
  · rw [distOneIn_cons_iff] at h
    rcases h with ⟨hx, w, r, hl, -⟩ | ⟨rfl, w, r, hl, hw⟩ | h
    · exact absurd hx h21
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (distOne_head hnd' h))
  · rw [distTwoIn_cons_iff] at h
    rcases h with ⟨hx, a, b, r, hl, -⟩ | ⟨rfl, a, b, r, hl, hw⟩ | h
    · exact absurd hx h21
    · exact absurd (hw.trans (List.cons.inj (List.cons.inj hl).2).1.symm) h23
    · exact Or.inr (Or.inr (distTwo_head hnd' h))



theorem gameGraph_append_singleton (G : SimpleGraph (Fin n))
    (l : List (Fin n)) (p : Fin n) :
    gameGraph G (l ++ [p]) = elimStep (gameGraph G l) p := by
  rw [gameGraph, List.foldl_append]
  rfl



theorem elimStep_adj_iff_of_ne {G : SimpleGraph (Fin n)} {p x y : Fin n}
    (hxy : x ≠ y) :
    (elimStep G p).Adj x y ↔ G.Adj x y ∨ (G.Adj x p ∧ G.Adj y p) := by
  simp only [elimStep, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, (h | ⟨h1, h2⟩) | (h | ⟨h1, h2⟩)⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨h2, h1⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact ⟨hxy, Or.inl (Or.inl h)⟩
    · exact ⟨hxy, Or.inl (Or.inr ⟨h1, h2⟩)⟩



/-- No game edge at a level forces a zero Schur entry there. -/
theorem schurEntry_eq_zero_of_not_gameAdj {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (l : List (Fin n)) (S : Finset (Fin n)) (henum : Enumerates l S)
    {x y : Fin n} (hxy : x ≠ y)
    (h : ¬ (gameGraph (patternGraph A) l).Adj x y) :
    schurEntry A S x y = 0 := by
  by_contra hne
  apply h
  rw [← henum.2] at hne
  exact numeric_le_gameGraph hA l x y
    (numericPattern_adj_mk _ x y hxy hne)



/-- A zero leg through the pivot leaves the entry unchanged. -/
theorem schurEntry_insert_eq_of_leg_zero {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (S : Finset (Fin n)) {p x y : Fin n} (hp : p ∉ S)
    (hx : x ∉ insert p S) (hy : y ∉ insert p S)
    (hleg : schurEntry A S x p = 0 ∨ schurEntry A S y p = 0) :
    schurEntry A (insert p S) x y = schurEntry A S x y := by
  rw [schur_quotient hA S p hp x y hx hy]
  rcases hleg with hh | hh <;> simp [pivotEntry, hh]




theorem distOneIn_comm {l : List (Fin n)} {x y : Fin n} :
    DistOneIn l x y ↔ DistOneIn l y x := by
  constructor <;> rintro (⟨l₁, l₂, hl⟩ | ⟨l₁, l₂, hl⟩)
  · exact Or.inr ⟨l₁, l₂, hl⟩
  · exact Or.inl ⟨l₁, l₂, hl⟩
  · exact Or.inr ⟨l₁, l₂, hl⟩
  · exact Or.inl ⟨l₁, l₂, hl⟩



theorem distTwoIn_comm {l : List (Fin n)} {x y : Fin n} :
    DistTwoIn l x y ↔ DistTwoIn l y x := by
  constructor <;> rintro (⟨l₁, l₂, m, hl⟩ | ⟨l₁, l₂, m, hl⟩)
  · exact Or.inr ⟨l₁, l₂, m, hl⟩
  · exact Or.inl ⟨l₁, l₂, m, hl⟩
  · exact Or.inr ⟨l₁, l₂, m, hl⟩
  · exact Or.inl ⟨l₁, l₂, m, hl⟩



/-- Appending one pivot to an enumeration. -/
theorem enumerates_append_singleton {lS : List (Fin n)}
    {S : Finset (Fin n)} {p : Fin n} (henum : Enumerates lS S)
    (hp : p ∉ S) : Enumerates (lS ++ [p]) (insert p S) := by
  refine ⟨?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨henum.1, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    subst hb
    subst hab
    exact hp (henum.2 ▸ List.mem_toFinset.mpr ha)
  · have h1 : ([p] : List (Fin n)).toFinset = {p} := by simp
    rw [List.toFinset_append, henum.2, h1, Finset.insert_eq,
      Finset.union_comm]



/-- Distance pairs of a cons list not involving the head are distance
pairs of the tail. -/
theorem dist_cons_tail_iff {z x y : Fin n} {l : List (Fin n)}
    (hzx : x ≠ z) (hzy : y ≠ z) :
    (DistOneIn (z :: l) x y ∨ DistTwoIn (z :: l) x y)
      ↔ (DistOneIn l x y ∨ DistTwoIn l x y) := by
  constructor
  · rintro (h | h)
    · rw [distOneIn_cons_iff] at h
      rcases h with ⟨hx2, -⟩ | ⟨hy2, -⟩ | h
      · exact absurd hx2 hzx
      · exact absurd hy2 hzy
      · exact Or.inl h
    · rw [distTwoIn_cons_iff] at h
      rcases h with ⟨hx2, -⟩ | ⟨hy2, -⟩ | h
      · exact absurd hx2 hzx
      · exact absurd hy2 hzy
      · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (distOneIn_cons_iff.mpr (Or.inr (Or.inr h)))
    · exact Or.inr (distTwoIn_cons_iff.mpr (Or.inr (Or.inr h)))



/-- In a strip state, the game neighbours of the head vertex are
exactly the next two vertices. -/
theorem strip_head_adj {A : Matrix (Fin n) (Fin n) ℝ}
    {lS : List (Fin n)} {S : Finset (Fin n)}
    {s₁ s₂ s₃ : Fin n} {rest : List (Fin n)}
    (hstate : IsStripState A lS S (s₁ :: s₂ :: s₃ :: rest))
    {y : Fin n} (hy : y ∈ s₁ :: s₂ :: s₃ :: rest) (hy1 : y ≠ s₁) :
    (gameGraph (patternGraph A) lS).Adj s₁ y → y = s₂ ∨ y = s₃ := by
  intro hAdj
  have hdist := (hstate.2.2.2 s₁ (by simp) y hy (Ne.symm hy1)).mp hAdj
  rcases hdist with h | h
  · exact Or.inl (distOne_head hstate.2.1 h)
  · exact Or.inr (distTwo_head hstate.2.1 h)



/-- In a strip state, the game neighbours of the second vertex are
exactly the first, third, and fourth vertices. -/
theorem strip_second_adj {A : Matrix (Fin n) (Fin n) ℝ}
    {lS : List (Fin n)} {S : Finset (Fin n)}
    {s₁ s₂ s₃ s₄ : Fin n} {rest : List (Fin n)}
    (hstate : IsStripState A lS S (s₁ :: s₂ :: s₃ :: s₄ :: rest))
    {y : Fin n} (hy : y ∈ s₁ :: s₂ :: s₃ :: s₄ :: rest) (hy2 : y ≠ s₂) :
    (gameGraph (patternGraph A) lS).Adj s₂ y
      → y = s₁ ∨ y = s₃ ∨ y = s₄ := by
  intro hAdj
  have hdist := (hstate.2.2.2 s₂ (by simp) y hy (Ne.symm hy2)).mp hAdj
  exact dist_second hstate.2.1 hdist



/-- The strip state after an END pivot at the head: the tail is
again a strip state at the enlarged level. -/
theorem stripState_end {A : Matrix (Fin n) (Fin n) ℝ}
    {lS : List (Fin n)} {S : Finset (Fin n)}
    {s₁ s₂ s₃ : Fin n} {rest : List (Fin n)}
    (hstate : IsStripState A lS S (s₁ :: s₂ :: s₃ :: rest)) :
    IsStripState A (lS ++ [s₁]) (insert s₁ S) (s₂ :: s₃ :: rest) := by
  obtain ⟨henum, hnd, hmem, hadj⟩ := hstate
  have hs₁S : s₁ ∉ S := (hmem s₁).mp (by simp)
  have hnot : s₁ ∉ s₂ :: s₃ :: rest := (List.nodup_cons.mp hnd).1
  refine ⟨enumerates_append_singleton henum hs₁S,
    (List.nodup_cons.mp hnd).2, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hxl : x ∈ s₁ :: s₂ :: s₃ :: rest :=
        List.mem_cons_of_mem _ hx
      have hxS : x ∉ S := (hmem x).mp hxl
      have hx1 : x ≠ s₁ := fun hh => hnot (hh ▸ hx)
      simp [Finset.mem_insert, hx1, hxS]
    · intro hx
      have hxS : x ∉ S := fun h => hx (Finset.mem_insert_of_mem h)
      have hx1 : x ≠ s₁ := fun hh =>
        hx (hh ▸ Finset.mem_insert_self s₁ S)
      have hxl : x ∈ s₁ :: s₂ :: s₃ :: rest := (hmem x).mpr hxS
      rcases List.mem_cons.mp hxl with hh | hh
      · exact absurd hh hx1
      · exact hh
  · intro x hx y hy hxy
    have hx1 : x ≠ s₁ := fun hh => hnot (hh ▸ hx)
    have hy1 : y ≠ s₁ := fun hh => hnot (hh ▸ hy)
    have hxl : x ∈ s₁ :: s₂ :: s₃ :: rest :=
      List.mem_cons_of_mem _ hx
    have hyl : y ∈ s₁ :: s₂ :: s₃ :: rest :=
      List.mem_cons_of_mem _ hy
    rw [gameGraph_append_singleton, elimStep_adj_iff_of_ne hxy,
      hadj x hxl y hyl hxy, dist_cons_tail_iff hx1 hy1]
    constructor
    · rintro (h | ⟨hxA, hyA⟩)
      · exact h
      · have hdx : x = s₂ ∨ x = s₃ := by
          have h2 := (hadj x hxl s₁ (by simp) hx1).mp hxA
          rcases h2 with hh | hh
          · exact Or.inl (distOne_head hnd (distOneIn_comm.mp hh))
          · exact Or.inr (distTwo_head hnd (distTwoIn_comm.mp hh))
        have hdy : y = s₂ ∨ y = s₃ := by
          have h2 := (hadj y hyl s₁ (by simp) hy1).mp hyA
          rcases h2 with hh | hh
          · exact Or.inl (distOne_head hnd (distOneIn_comm.mp hh))
          · exact Or.inr (distTwo_head hnd (distTwoIn_comm.mp hh))
        rcases hdx with rfl | rfl <;> rcases hdy with rfl | rfl
        · exact absurd rfl hxy
        · exact Or.inl (Or.inl ⟨[], rest, rfl⟩)
        · exact Or.inl (Or.inr ⟨[], rest, rfl⟩)
        · exact absurd rfl hxy
    · intro h
      exact Or.inl h



/-- A Schur entry between two tail vertices other than the
`(s₂, s₃)` pair is unchanged by an END pivot at `s₁`. -/
theorem strip_entry_end_of_ne {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {lS : List (Fin n)}
    {S : Finset (Fin n)} {s₁ s₂ s₃ : Fin n} {rest : List (Fin n)}
    (hstate : IsStripState A lS S (s₁ :: s₂ :: s₃ :: rest))
    {x y : Fin n} (hx : x ∈ s₂ :: s₃ :: rest)
    (hy : y ∈ s₂ :: s₃ :: rest) (hxy : x ≠ y)
    (hpair : ¬ SamePair x y s₂ s₃) :
    schurEntry A (insert s₁ S) x y = schurEntry A S x y := by
  obtain ⟨henum, hnd, hmem, hadj⟩ := hstate
  have hnot : s₁ ∉ s₂ :: s₃ :: rest := (List.nodup_cons.mp hnd).1
  have hs₁S : s₁ ∉ S := (hmem s₁).mp (by simp)
  have hx1 : x ≠ s₁ := fun hh => hnot (hh ▸ hx)
  have hy1 : y ≠ s₁ := fun hh => hnot (hh ▸ hy)
  have hxl : x ∈ s₁ :: s₂ :: s₃ :: rest := List.mem_cons_of_mem _ hx
  have hyl : y ∈ s₁ :: s₂ :: s₃ :: rest := List.mem_cons_of_mem _ hy
  have hxout : x ∉ insert s₁ S := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hx1, (hmem x).mp hxl⟩
  have hyout : y ∉ insert s₁ S := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hy1, (hmem y).mp hyl⟩
  have hleg : ∀ z ∈ s₂ :: s₃ :: rest, z ≠ s₂ → z ≠ s₃ →
      schurEntry A S z s₁ = 0 := by
    intro z hz hz2 hz3
    refine schurEntry_eq_zero_of_not_gameAdj hA lS S henum
      (x := z) (y := s₁) (fun hh => hnot (hh ▸ hz)) ?_
    intro hAdj
    have hzl : z ∈ s₁ :: s₂ :: s₃ :: rest :=
      List.mem_cons_of_mem _ hz
    have hz1 : z ≠ s₁ := fun hh => hnot (hh ▸ hz)
    have := strip_head_adj ⟨henum, hnd, hmem, hadj⟩ hzl hz1 hAdj.symm
    rcases this with hh | hh
    · exact hz2 hh
    · exact hz3 hh
  apply schurEntry_insert_eq_of_leg_zero hA S hs₁S hxout hyout
  by_cases hx2 : x = s₂
  · by_cases hy3 : y = s₃
    · subst hx2
      subst hy3
      exact absurd (Or.inl ⟨rfl, rfl⟩) hpair
    · exact Or.inr (hleg y hy (fun hh => hxy (hx2.trans hh.symm)) hy3)
  · by_cases hx3 : x = s₃
    · by_cases hy2 : y = s₂
      · subst hx3
        subst hy2
        exact absurd (Or.inr ⟨rfl, rfl⟩) hpair
      · exact Or.inr (hleg y hy hy2 (fun hh => hxy (hx3.trans hh.symm)))
    · exact Or.inl (hleg x hx hx2 hx3)



/-- An `AfterIn` pair forces list length at least two. -/
theorem afterIn_length_ge {l : List (Fin n)} {p x : Fin n}
    (h : AfterIn l p x) : 2 ≤ l.length := by
  obtain ⟨l₁, l₂, l₃, hl⟩ := h
  have h2 := congrArg List.length hl
  simp only [List.length_append, List.length_cons] at h2
  omega



/-- A two-survivor clean continuation. -/
theorem admitsCleanContinuation_two
    {A : Matrix (Fin n) (Fin n) ℝ} {lS : List (Fin n)} {S : Finset (Fin n)} {a b : Fin n}
    (henum : Enumerates lS S)
    (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b)
    (hmem : ∀ x : Fin n, x ∉ S → x = a ∨ x = b)
    (hentry : (gameGraph (patternGraph A) lS).Adj a b
      → schurEntry A S a b ≠ 0) :
    AdmitsCleanContinuation A lS S := by
  classical
  refine ⟨henum, [a, b], by simp [hab], ?_, ?_⟩
  · intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (rfl | rfl)
      · exact ha
      · exact hb
    · exact fun h => hmem x h
  · intro p x hAfter hAdj
    obtain ⟨l₁, l₂, l₃, hl⟩ := hAfter
    have hlen : l₁.length + l₂.length + l₃.length = 0 := by
      have h2 := congrArg List.length hl
      simp only [List.length_append, List.length_cons,
        List.length_nil] at h2
      omega
    have h1 : l₁ = [] := List.length_eq_zero_iff.mp (by omega)
    have h2 : l₂ = [] := List.length_eq_zero_iff.mp (by omega)
    have h3 : l₃ = [] := List.length_eq_zero_iff.mp (by omega)
    subst h1
    subst h2
    subst h3
    simp only [List.nil_append, List.cons_append] at hl
    obtain ⟨rfl, hrest⟩ := List.cons.inj hl
    obtain ⟨rfl, -⟩ := List.cons.inj hrest
    have hpre : prefixListBefore ([a, b] : List (Fin n)) a = [] := by
      simp [prefixListBefore]
    rw [hpre] at hAdj ⊢
    simp only [List.append_nil, List.toFinset_nil, Finset.union_empty]
      at hAdj ⊢
    exact hentry hAdj



/-- Strip states on at most two survivors admit clean continuations
with the strip list itself as the ordering. -/
theorem strip_continuation_small {A : Matrix (Fin n) (Fin n) ℝ}
    {lS : List (Fin n)}
    {S : Finset (Fin n)} {l : List (Fin n)} (hlen : l.length ≤ 2)
    (hstate : IsStripState A lS S l)
    (hst : StripStateZero A S l ∨ StripStateOne A S l) :
    AdmitsCleanContinuation A lS S := by
  classical
  obtain ⟨henum, hnd, hmem, hadj⟩ := hstate
  refine ⟨henum, l, hnd, hmem, ?_⟩
  intro p x hAfter hAdj
  obtain ⟨l₁, l₂, l₃, hl⟩ := hAfter
  have hlen0 : l₁.length + l₂.length + l₃.length = 0 := by
    have h2 := congrArg List.length hl
    simp only [List.length_append, List.length_cons] at h2
    omega
  have h1 : l₁ = [] := List.length_eq_zero_iff.mp (by omega)
  have h2 : l₂ = [] := List.length_eq_zero_iff.mp (by omega)
  have h3 : l₃ = [] := List.length_eq_zero_iff.mp (by omega)
  have hlpx : l = [p, x] := by
    rw [hl, h1, h2, h3]
    simp
  have hpre : prefixListBefore l p = [] := by
    rw [hlpx]
    simp [prefixListBefore]
  rw [hpre] at hAdj ⊢
  simp only [List.append_nil, List.toFinset_nil, Finset.union_empty]
    at hAdj ⊢
  have hp : p ∈ l := by rw [hlpx]; simp
  have hx : x ∈ l := by rw [hlpx]; simp
  have hdist := (hadj p hp x hx hAdj.ne).mp hAdj
  rcases hst with h0 | h1
  · exact h0 p x hdist
  · obtain ⟨s₁, s₂, s₃, rest, hl1, -, -⟩ := h1
    rw [hl1] at hlen
    simp at hlen




/-- The strip state after a SECOND pivot at the second vertex: the
list `s₁, s₃, s₄, …` is again a strip state at the enlarged level. -/
theorem stripState_second {A : Matrix (Fin n) (Fin n) ℝ}
    {lS : List (Fin n)} {S : Finset (Fin n)}
    {s₁ s₂ s₃ s₄ : Fin n} {rest : List (Fin n)}
    (hstate : IsStripState A lS S (s₁ :: s₂ :: s₃ :: s₄ :: rest)) :
    IsStripState A (lS ++ [s₂]) (insert s₂ S)
      (s₁ :: s₃ :: s₄ :: rest) := by
  obtain ⟨henum, hnd, hmem, hadj⟩ := hstate
  have hnot1 : s₁ ∉ s₂ :: s₃ :: s₄ :: rest :=
    (List.nodup_cons.mp hnd).1
  have hnd2 : (s₂ :: s₃ :: s₄ :: rest).Nodup :=
    (List.nodup_cons.mp hnd).2
  have hnot2 : s₂ ∉ s₃ :: s₄ :: rest := (List.nodup_cons.mp hnd2).1
  have hnd3 : (s₃ :: s₄ :: rest).Nodup :=
    (List.nodup_cons.mp hnd2).2
  have hnot3 : s₃ ∉ s₄ :: rest := (List.nodup_cons.mp hnd3).1
  have h12 : s₁ ≠ s₂ := fun hh => hnot1 (by simp [hh])
  have h13 : s₁ ≠ s₃ := fun hh => hnot1 (by simp [hh])
  have h14 : s₁ ≠ s₄ := fun hh => hnot1 (by simp [hh])
  have h23 : s₂ ≠ s₃ := fun hh => hnot2 (by simp [hh])
  have h24 : s₂ ≠ s₄ := fun hh => hnot2 (by simp [hh])
  have h34 : s₃ ≠ s₄ := fun hh => hnot3 (by simp [hh])
  have hs₂S : s₂ ∉ S := (hmem s₂).mp (by simp)
  have hnd' : (s₁ :: s₃ :: s₄ :: rest).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, hnd3⟩
    intro h
    exact hnot1 (List.mem_cons_of_mem _ h)
  have hnot2' : s₂ ∉ s₁ :: s₃ :: s₄ :: rest := by
    intro h
    rcases List.mem_cons.mp h with hh | hh
    · exact (Ne.symm h12) hh
    · exact hnot2 hh
  have hmem' : ∀ x : Fin n, x ∈ s₁ :: s₃ :: s₄ :: rest
      ↔ x ∉ insert s₂ S := by
    intro x
    constructor
    · intro hx
      have hxl : x ∈ s₁ :: s₂ :: s₃ :: s₄ :: rest := by
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
      have hxS : x ∉ S := (hmem x).mp hxl
      have hx2 : x ≠ s₂ := fun hh => hnot2' (hh ▸ hx)
      simp [Finset.mem_insert, hx2, hxS]
    · intro hx
      have hxS : x ∉ S := fun h => hx (Finset.mem_insert_of_mem h)
      have hx2 : x ≠ s₂ := fun hh =>
        hx (hh ▸ Finset.mem_insert_self s₂ S)
      have hxl : x ∈ s₁ :: s₂ :: s₃ :: s₄ :: rest :=
        (hmem x).mpr hxS
      rcases List.mem_cons.mp hxl with rfl | hx3
      · simp
      · rcases List.mem_cons.mp hx3 with hh | hh
        · exact absurd hh hx2
        · exact List.mem_cons_of_mem _ hh
  refine ⟨enumerates_append_singleton henum hs₂S, hnd', hmem', ?_⟩
  intro x hx y hy hxy
  have hx2 : x ≠ s₂ := fun hh => hnot2' (hh ▸ hx)
  have hy2 : y ≠ s₂ := fun hh => hnot2' (hh ▸ hy)
  have hxl : x ∈ s₁ :: s₂ :: s₃ :: s₄ :: rest := by
    have := (hmem' x).mp hx
    exact (hmem x).mpr (fun h => this (Finset.mem_insert_of_mem h))
  have hyl : y ∈ s₁ :: s₂ :: s₃ :: s₄ :: rest := by
    have := (hmem' y).mp hy
    exact (hmem y).mpr (fun h => this (Finset.mem_insert_of_mem h))
  -- dist witnesses used repeatedly
  have hd12 : DistOneIn (s₁ :: s₂ :: s₃ :: s₄ :: rest) s₁ s₂ :=
    distOneIn_cons_iff.mpr
      (Or.inl ⟨rfl, s₂, s₃ :: s₄ :: rest, rfl, rfl⟩)
  have hd13 : DistTwoIn (s₁ :: s₂ :: s₃ :: s₄ :: rest) s₁ s₃ :=
    distTwoIn_cons_iff.mpr
      (Or.inl ⟨rfl, s₂, s₃, s₄ :: rest, rfl, rfl⟩)
  have hd24 : DistTwoIn (s₁ :: s₂ :: s₃ :: s₄ :: rest) s₂ s₄ :=
    distTwoIn_cons_iff.mpr (Or.inr (Or.inr
      (distTwoIn_cons_iff.mpr
        (Or.inl ⟨rfl, s₃, s₄, rest, rfl, rfl⟩))))
  have hd34' : DistOneIn (s₁ :: s₃ :: s₄ :: rest) s₃ s₄ :=
    distOneIn_cons_iff.mpr (Or.inr (Or.inr
      (distOneIn_cons_iff.mpr
        (Or.inl ⟨rfl, s₄, rest, rfl, rfl⟩))))
  have hd13' : DistOneIn (s₁ :: s₃ :: s₄ :: rest) s₁ s₃ :=
    distOneIn_cons_iff.mpr
      (Or.inl ⟨rfl, s₃, s₄ :: rest, rfl, rfl⟩)
  have hd14' : DistTwoIn (s₁ :: s₃ :: s₄ :: rest) s₁ s₄ :=
    distTwoIn_cons_iff.mpr
      (Or.inl ⟨rfl, s₃, s₄, rest, rfl, rfl⟩)
  -- (a) dist in l implies dist in l'
  have hA : (DistOneIn (s₁ :: s₂ :: s₃ :: s₄ :: rest) x y
        ∨ DistTwoIn (s₁ :: s₂ :: s₃ :: s₄ :: rest) x y)
      → (DistOneIn (s₁ :: s₃ :: s₄ :: rest) x y
        ∨ DistTwoIn (s₁ :: s₃ :: s₄ :: rest) x y) := by
    rintro (h | h)
    · by_cases hx1 : x = s₁
      · subst hx1
        exact absurd (distOne_head hnd h) hy2
      by_cases hy1 : y = s₁
      · subst hy1
        exact absurd (distOne_head hnd (distOneIn_comm.mp h)) hx2
      · have h' : DistOneIn (s₃ :: s₄ :: rest) x y := by
          have step1 : DistOneIn (s₂ :: s₃ :: s₄ :: rest) x y := by
            rw [distOneIn_cons_iff] at h
            rcases h with ⟨hxx, -⟩ | ⟨hyy, -⟩ | h
            · exact absurd hxx hx1
            · exact absurd hyy hy1
            · exact h
          rw [distOneIn_cons_iff] at step1
          rcases step1 with ⟨hxx, -⟩ | ⟨hyy, -⟩ | h
          · exact absurd hxx hx2
          · exact absurd hyy hy2
          · exact h
        exact Or.inl (distOneIn_cons_iff.mpr (Or.inr (Or.inr h')))
    · by_cases hx1 : x = s₁
      · subst hx1
        have hy3 : y = s₃ := distTwo_head hnd h
        subst hy3
        exact Or.inl hd13'
      by_cases hy1 : y = s₁
      · subst hy1
        have hx3 : x = s₃ := distTwo_head hnd (distTwoIn_comm.mp h)
        subst hx3
        exact Or.inl (distOneIn_comm.mp hd13')
      · have h' : DistTwoIn (s₃ :: s₄ :: rest) x y := by
          have step1 : DistTwoIn (s₂ :: s₃ :: s₄ :: rest) x y := by
            rw [distTwoIn_cons_iff] at h
            rcases h with ⟨hxx, -⟩ | ⟨hyy, -⟩ | h
            · exact absurd hxx hx1
            · exact absurd hyy hy1
            · exact h
          rw [distTwoIn_cons_iff] at step1
          rcases step1 with ⟨hxx, -⟩ | ⟨hyy, -⟩ | h
          · exact absurd hxx hx2
          · exact absurd hyy hy2
          · exact h
        exact Or.inr (distTwoIn_cons_iff.mpr (Or.inr (Or.inr h')))
  -- (b) dist in l' implies dist in l or both adjacent to s₂
  have hB : (DistOneIn (s₁ :: s₃ :: s₄ :: rest) x y
        ∨ DistTwoIn (s₁ :: s₃ :: s₄ :: rest) x y)
      → (DistOneIn (s₁ :: s₂ :: s₃ :: s₄ :: rest) x y
          ∨ DistTwoIn (s₁ :: s₂ :: s₃ :: s₄ :: rest) x y)
        ∨ ((gameGraph (patternGraph A) lS).Adj x s₂
          ∧ (gameGraph (patternGraph A) lS).Adj y s₂) := by
    have hAdj12 : (gameGraph (patternGraph A) lS).Adj s₁ s₂ :=
      (hadj s₁ (by simp) s₂ (by simp) h12).mpr (Or.inl hd12)
    have hAdj42 : (gameGraph (patternGraph A) lS).Adj s₄ s₂ :=
      (hadj s₄ (by simp) s₂ (by simp) (Ne.symm h24)).mpr
        (Or.inr (distTwoIn_comm.mp hd24))
    rintro (h | h)
    · by_cases hx1 : x = s₁
      · subst hx1
        have hy3 : y = s₃ := distOne_head hnd' h
        subst hy3
        exact Or.inl (Or.inr hd13)
      by_cases hy1 : y = s₁
      · subst hy1
        have hx3 : x = s₃ := distOne_head hnd' (distOneIn_comm.mp h)
        subst hx3
        exact Or.inl (Or.inr (distTwoIn_comm.mp hd13))
      · have h' : DistOneIn (s₃ :: s₄ :: rest) x y := by
          rw [distOneIn_cons_iff] at h
          rcases h with ⟨hxx, -⟩ | ⟨hyy, -⟩ | h
          · exact absurd hxx hx1
          · exact absurd hyy hy1
          · exact h
        exact Or.inl (Or.inl (distOneIn_cons_iff.mpr (Or.inr (Or.inr
          (distOneIn_cons_iff.mpr (Or.inr (Or.inr h')))))))
    · by_cases hx1 : x = s₁
      · subst hx1
        have hy4 : y = s₄ := distTwo_head hnd' h
        subst hy4
        exact Or.inr ⟨hAdj12, hAdj42⟩
      by_cases hy1 : y = s₁
      · subst hy1
        have hx4 : x = s₄ := distTwo_head hnd' (distTwoIn_comm.mp h)
        subst hx4
        exact Or.inr ⟨hAdj42, hAdj12⟩
      · have h' : DistTwoIn (s₃ :: s₄ :: rest) x y := by
          rw [distTwoIn_cons_iff] at h
          rcases h with ⟨hxx, -⟩ | ⟨hyy, -⟩ | h
          · exact absurd hxx hx1
          · exact absurd hyy hy1
          · exact h
        exact Or.inl (Or.inr (distTwoIn_cons_iff.mpr (Or.inr (Or.inr
          (distTwoIn_cons_iff.mpr (Or.inr (Or.inr h')))))))
  -- (c) both adjacent to s₂ implies dist in l'
  have hC : (gameGraph (patternGraph A) lS).Adj x s₂
        ∧ (gameGraph (patternGraph A) lS).Adj y s₂
      → (DistOneIn (s₁ :: s₃ :: s₄ :: rest) x y
        ∨ DistTwoIn (s₁ :: s₃ :: s₄ :: rest) x y) := by
    rintro ⟨hxA, hyA⟩
    have hdx : x = s₁ ∨ x = s₃ ∨ x = s₄ :=
      strip_second_adj ⟨henum, hnd, hmem, hadj⟩ hxl hx2 hxA.symm
    have hdy : y = s₁ ∨ y = s₃ ∨ y = s₄ :=
      strip_second_adj ⟨henum, hnd, hmem, hadj⟩ hyl hy2 hyA.symm
    rcases hdx with rfl | rfl | rfl <;> rcases hdy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact Or.inl hd13'
    · exact Or.inr hd14'
    · exact Or.inl (distOneIn_comm.mp hd13')
    · exact absurd rfl hxy
    · exact Or.inl hd34'
    · exact Or.inr (distTwoIn_comm.mp hd14')
    · exact Or.inl (distOneIn_comm.mp hd34')
    · exact absurd rfl hxy
  rw [gameGraph_append_singleton, elimStep_adj_iff_of_ne hxy,
    hadj x hxl y hyl hxy]
  constructor
  · rintro (h | hboth)
    · exact hA h
    · exact hC hboth
  · intro h
    rcases hB h with h | hboth
    · exact Or.inl h
    · exact Or.inr hboth



/-- A Schur entry at a pair of the new strip list with at least one
endpoint outside `{s₁, s₃, s₄}` is unchanged by a SECOND pivot. -/
theorem strip_entry_second_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {lS : List (Fin n)}
    {S : Finset (Fin n)} {s₁ s₂ s₃ s₄ : Fin n} {rest : List (Fin n)}
    (hstate : IsStripState A lS S (s₁ :: s₂ :: s₃ :: s₄ :: rest))
    {x y : Fin n} (hx : x ∈ s₁ :: s₃ :: s₄ :: rest)
    (hy : y ∈ s₁ :: s₃ :: s₄ :: rest) (_hxy : x ≠ y)
    (hout : (x ≠ s₁ ∧ x ≠ s₃ ∧ x ≠ s₄)
      ∨ (y ≠ s₁ ∧ y ≠ s₃ ∧ y ≠ s₄)) :
    schurEntry A (insert s₂ S) x y = schurEntry A S x y := by
  obtain ⟨henum, hnd, hmem, hadj⟩ := hstate
  have hnot1 : s₁ ∉ s₂ :: s₃ :: s₄ :: rest :=
    (List.nodup_cons.mp hnd).1
  have hnd2 : (s₂ :: s₃ :: s₄ :: rest).Nodup :=
    (List.nodup_cons.mp hnd).2
  have hnot2 : s₂ ∉ s₃ :: s₄ :: rest := (List.nodup_cons.mp hnd2).1
  have h12 : s₁ ≠ s₂ := fun hh => hnot1 (by simp [hh])
  have hnot2' : s₂ ∉ s₁ :: s₃ :: s₄ :: rest := by
    intro h
    rcases List.mem_cons.mp h with hh | hh
    · exact (Ne.symm h12) hh
    · exact hnot2 hh
  have hs₂S : s₂ ∉ S := (hmem s₂).mp (by simp)
  have hx2 : x ≠ s₂ := fun hh => hnot2' (hh ▸ hx)
  have hy2 : y ≠ s₂ := fun hh => hnot2' (hh ▸ hy)
  have hxl : x ∈ s₁ :: s₂ :: s₃ :: s₄ :: rest := by
    rcases List.mem_cons.mp hx with rfl | hx3
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx3)
  have hyl : y ∈ s₁ :: s₂ :: s₃ :: s₄ :: rest := by
    rcases List.mem_cons.mp hy with rfl | hy3
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy3)
  have hxout : x ∉ insert s₂ S := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hx2, (hmem x).mp hxl⟩
  have hyout : y ∉ insert s₂ S := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hy2, (hmem y).mp hyl⟩
  have hleg : ∀ z ∈ s₁ :: s₃ :: s₄ :: rest,
      z ≠ s₁ → z ≠ s₃ → z ≠ s₄ → schurEntry A S z s₂ = 0 := by
    intro z hz hz1 hz3 hz4
    have hz2 : z ≠ s₂ := fun hh => hnot2' (hh ▸ hz)
    have hzl : z ∈ s₁ :: s₂ :: s₃ :: s₄ :: rest := by
      rcases List.mem_cons.mp hz with rfl | hz3'
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz3')
    refine schurEntry_eq_zero_of_not_gameAdj hA lS S henum
      (x := z) (y := s₂) hz2 ?_
    intro hAdj
    have := strip_second_adj ⟨henum, hnd, hmem, hadj⟩ hzl hz2
      hAdj.symm
    rcases this with hh | hh | hh
    · exact hz1 hh
    · exact hz3 hh
    · exact hz4 hh
  apply schurEntry_insert_eq_of_leg_zero hA S hs₂S hxout hyout
  rcases hout with ⟨h1, h3, h4⟩ | ⟨h1, h3, h4⟩
  · exact Or.inl (hleg x hx h1 h3 h4)
  · exact Or.inr (hleg y hy h1 h3 h4)

end CholeskyCancellations

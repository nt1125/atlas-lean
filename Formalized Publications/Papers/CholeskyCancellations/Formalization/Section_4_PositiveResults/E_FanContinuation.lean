/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.TakeWhile
import Section_4_PositiveResults.D_StripContinuation

/-! # Fan continuation (paper Section 4)

Fan patterns and states, the fan state machine (`fan_continuation`), and the per-matrix fan class theorem (`fans_perMatrix`, Theorem 4.8). Split from `Positives.lean`.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as `Defs.lean`; graph classes are predicates on `SimpleGraph (Fin n)` patterns and cleanliness is quantified per SPD realization through `PatternAdmitsPerMatrixCleanOrdering`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}



/-- `IsFanPattern G`: `G` is a dominating-vertex fan — a center
adjacent to every other vertex, with the remaining vertices forming
a path (paper Theorem 4.8 (i), "Fans (dominating-vertex fan)" in its
proof, `thm:positives`). -/
def IsFanPattern (G : SimpleGraph (Fin n)) : Prop :=
  ∃ c : Fin n, ∃ l : List (Fin n),
    l.Nodup ∧ (∀ x : Fin n, x ∈ l ↔ x ≠ c) ∧
      (∀ v : Fin n, v ≠ c → G.Adj c v) ∧
      ∀ x y : Fin n, x ≠ c → y ≠ c → (G.Adj x y ↔ DistOneIn l x y)



/-- `IsFanState A lS S c l`: `(S, P)` is a fan state — the symbolic
graph at level `S` is a dominating-vertex fan with center `c` and
path list `l` (fan states of the proof of paper Theorem 4.8 (i)). -/
def IsFanState (A : Matrix (Fin n) (Fin n) ℝ) (lS : List (Fin n))
    (S : Finset (Fin n)) (c : Fin n) (l : List (Fin n)) : Prop :=
  Enumerates lS S ∧ c ∉ S ∧ l.Nodup ∧
    (∀ x : Fin n, x ∈ l ↔ x ∉ S ∧ x ≠ c) ∧
    (∀ x ∈ l, (gameGraph (patternGraph A) lS).Adj c x) ∧
    ∀ x ∈ l, ∀ y ∈ l, x ≠ y →
      ((gameGraph (patternGraph A) lS).Adj x y ↔ DistOneIn l x y)



/-- Fan State 0: every center edge and path edge is nonzero. -/
def FanStateZero (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (c : Fin n) (l : List (Fin n)) : Prop :=
  (∀ x ∈ l, schurEntry A S c x ≠ 0)
    ∧ ∀ x y : Fin n, DistOneIn l x y → schurEntry A S x y ≠ 0



/-- Fan State 1: exactly the center edge at the second path vertex
is zero. -/
def FanStateOne (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (c : Fin n) (l : List (Fin n)) : Prop :=
  ∃ s₁ s₂ : Fin n, ∃ rest : List (Fin n), l = s₁ :: s₂ :: rest ∧
    schurEntry A S c s₂ = 0 ∧
    (∀ x ∈ l, x ≠ s₂ → schurEntry A S c x ≠ 0)
      ∧ ∀ x y : Fin n, DistOneIn l x y → schurEntry A S x y ≠ 0



/-- In a fan state, the only path neighbour of the head vertex is
the second vertex. -/
theorem fan_head_adj {A : Matrix (Fin n) (Fin n) ℝ}
    {lS : List (Fin n)} {S : Finset (Fin n)}
    {c s₁ s₂ : Fin n} {rest : List (Fin n)}
    (hstate : IsFanState A lS S c (s₁ :: s₂ :: rest)) {y : Fin n}
    (hy : y ∈ s₁ :: s₂ :: rest) (hy1 : y ≠ s₁)
    (hyA : (gameGraph (patternGraph A) lS).Adj s₁ y) : y = s₂ := by
  obtain ⟨-, -, hnd, -, -, hadj⟩ := hstate
  exact distOne_head hnd
    ((hadj s₁ (by simp) y hy (Ne.symm hy1)).mp hyA)



/-- In a fan state, the only path neighbours of the second vertex
are the first and third. -/
theorem fan_second_adj {A : Matrix (Fin n) (Fin n) ℝ}
    {lS : List (Fin n)} {S : Finset (Fin n)}
    {c s₁ s₂ s₃ : Fin n} {rest : List (Fin n)}
    (hstate : IsFanState A lS S c (s₁ :: s₂ :: s₃ :: rest))
    {y : Fin n} (hy : y ∈ s₁ :: s₂ :: s₃ :: rest) (hy2 : y ≠ s₂)
    (hyA : (gameGraph (patternGraph A) lS).Adj s₂ y) :
    y = s₁ ∨ y = s₃ := by
  obtain ⟨-, -, hnd, -, -, hadj⟩ := hstate
  have hnd2 : (s₂ :: s₃ :: rest).Nodup :=
    (List.nodup_cons.mp hnd).2
  have h21 : s₂ ≠ s₁ := by
    have hnot := (List.nodup_cons.mp hnd).1
    intro hh
    exact hnot (hh ▸ by simp)
  have h := (hadj s₂ (by simp) y hy (Ne.symm hy2)).mp hyA
  rw [distOneIn_cons_iff] at h
  rcases h with ⟨hx, -⟩ | ⟨rfl, -, -⟩ | h
  · exact absurd hx h21
  · exact Or.inl rfl
  · exact Or.inr (distOne_head hnd2 h)



/-- The fan state after an END pivot at the head path vertex. -/
theorem fanState_end {A : Matrix (Fin n) (Fin n) ℝ}
    {lS : List (Fin n)} {S : Finset (Fin n)}
    {c s₁ s₂ : Fin n} {rest : List (Fin n)}
    (hstate : IsFanState A lS S c (s₁ :: s₂ :: rest)) :
    IsFanState A (lS ++ [s₁]) (insert s₁ S) c (s₂ :: rest) := by
  have hstate0 := hstate
  obtain ⟨henum, hcS, hnd, hmem, hcenter, hadj⟩ := hstate
  have hnot : s₁ ∉ s₂ :: rest := (List.nodup_cons.mp hnd).1
  have hs₁S : s₁ ∉ S := ((hmem s₁).mp (by simp)).1
  have hs₁c : s₁ ≠ c := ((hmem s₁).mp (by simp)).2
  refine ⟨enumerates_append_singleton henum hs₁S, ?_,
    (List.nodup_cons.mp hnd).2, ?_, ?_, ?_⟩
  · exact fun h => (Finset.mem_insert.mp h).elim
      (fun hh => hs₁c hh.symm) hcS
  · intro x
    constructor
    · intro hx
      have hxl : x ∈ s₁ :: s₂ :: rest := List.mem_cons_of_mem _ hx
      obtain ⟨hxS, hxc⟩ := (hmem x).mp hxl
      have hx1 : x ≠ s₁ := fun hh => hnot (hh ▸ hx)
      exact ⟨fun h => (Finset.mem_insert.mp h).elim
        (fun hh => hx1 hh) hxS, hxc⟩
    · rintro ⟨hxS, hxc⟩
      have hxS' : x ∉ S :=
        fun h => hxS (Finset.mem_insert_of_mem h)
      have hx1 : x ≠ s₁ :=
        fun hh => hxS (hh ▸ Finset.mem_insert_self s₁ S)
      have hxl : x ∈ s₁ :: s₂ :: rest :=
        (hmem x).mpr ⟨hxS', hxc⟩
      rcases List.mem_cons.mp hxl with hh | hh
      · exact absurd hh hx1
      · exact hh
  · intro x hx
    rw [gameGraph_append_singleton]
    exact elimStep_adj_of_adj _ _ _ _
      (hcenter x (List.mem_cons_of_mem _ hx))
  · intro x hx y hy hxy
    have hx1 : x ≠ s₁ := fun hh => hnot (hh ▸ hx)
    have hy1 : y ≠ s₁ := fun hh => hnot (hh ▸ hy)
    have hxl : x ∈ s₁ :: s₂ :: rest := List.mem_cons_of_mem _ hx
    have hyl : y ∈ s₁ :: s₂ :: rest := List.mem_cons_of_mem _ hy
    rw [gameGraph_append_singleton, elimStep_adj_iff_of_ne hxy,
      hadj x hxl y hyl hxy]
    constructor
    · rintro (h | ⟨hxA, hyA⟩)
      · rw [distOneIn_cons_iff] at h
        rcases h with ⟨hx2, -⟩ | ⟨hy2, -⟩ | h
        · exact absurd hx2 hx1
        · exact absurd hy2 hy1
        · exact h
      · have hdx : x = s₂ := by
          have h2 := (hadj x hxl s₁ (by simp) hx1).mp hxA
          exact distOne_head hnd (distOneIn_comm.mp h2)
        have hdy : y = s₂ := by
          have h2 := (hadj y hyl s₁ (by simp) hy1).mp hyA
          exact distOne_head hnd (distOneIn_comm.mp h2)
        exact absurd (hdx.trans hdy.symm) hxy
    · intro h
      exact Or.inl (distOneIn_cons_iff.mpr (Or.inr (Or.inr h)))



/-- The fan state after a SECOND pivot at the second path vertex. -/
theorem fanState_second {A : Matrix (Fin n) (Fin n) ℝ}
    {lS : List (Fin n)} {S : Finset (Fin n)}
    {c s₁ s₂ s₃ : Fin n} {rest : List (Fin n)}
    (hstate : IsFanState A lS S c (s₁ :: s₂ :: s₃ :: rest)) :
    IsFanState A (lS ++ [s₂]) (insert s₂ S) c (s₁ :: s₃ :: rest) := by
  have hstate0 := hstate
  obtain ⟨henum, hcS, hnd, hmem, hcenter, hadj⟩ := hstate
  have hnot1 : s₁ ∉ s₂ :: s₃ :: rest := (List.nodup_cons.mp hnd).1
  have hnd2 : (s₂ :: s₃ :: rest).Nodup :=
    (List.nodup_cons.mp hnd).2
  have hnot2 : s₂ ∉ s₃ :: rest := (List.nodup_cons.mp hnd2).1
  have hnd3 : (s₃ :: rest).Nodup := (List.nodup_cons.mp hnd2).2
  have h12 : s₁ ≠ s₂ := fun hh => hnot1 (by simp [hh])
  have h13 : s₁ ≠ s₃ := fun hh => hnot1 (by simp [hh])
  have h23 : s₂ ≠ s₃ := fun hh => hnot2 (by simp [hh])
  have hs₂S : s₂ ∉ S := ((hmem s₂).mp (by simp)).1
  have hs₁S : s₁ ∉ S := ((hmem s₁).mp (by simp)).1
  have hnd' : (s₁ :: s₃ :: rest).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, hnd3⟩
    intro h
    exact hnot1 (List.mem_cons_of_mem _ h)
  have hnot2' : s₂ ∉ s₁ :: s₃ :: rest := by
    intro h
    rcases List.mem_cons.mp h with hh | hh
    · exact (Ne.symm h12) hh
    · exact hnot2 hh
  refine ⟨enumerates_append_singleton henum hs₂S, ?_, hnd', ?_, ?_,
    ?_⟩
  · exact fun h => (Finset.mem_insert.mp h).elim
      (fun hh => ((hmem s₂).mp (by simp)).2 hh.symm) hcS
  · intro x
    constructor
    · intro hx
      have hxl : x ∈ s₁ :: s₂ :: s₃ :: rest := by
        rcases List.mem_cons.mp hx with rfl | hx3
        · simp
        · exact List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hx3)
      obtain ⟨hxS, hxc⟩ := (hmem x).mp hxl
      have hx2 : x ≠ s₂ := fun hh => hnot2' (hh ▸ hx)
      exact ⟨fun h => (Finset.mem_insert.mp h).elim
        (fun hh => hx2 hh) hxS, hxc⟩
    · rintro ⟨hxS, hxc⟩
      have hxS' : x ∉ S :=
        fun h => hxS (Finset.mem_insert_of_mem h)
      have hx2 : x ≠ s₂ :=
        fun hh => hxS (hh ▸ Finset.mem_insert_self s₂ S)
      have hxl : x ∈ s₁ :: s₂ :: s₃ :: rest :=
        (hmem x).mpr ⟨hxS', hxc⟩
      rcases List.mem_cons.mp hxl with rfl | hx3
      · simp
      · rcases List.mem_cons.mp hx3 with hh | hh
        · exact absurd hh hx2
        · exact List.mem_cons_of_mem _ hh
  · intro x hx
    rw [gameGraph_append_singleton]
    refine elimStep_adj_of_adj _ _ _ _ (hcenter x ?_)
    rcases List.mem_cons.mp hx with rfl | hx3
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx3)
  · intro x hx y hy hxy
    have hx2 : x ≠ s₂ := fun hh => hnot2' (hh ▸ hx)
    have hy2 : y ≠ s₂ := fun hh => hnot2' (hh ▸ hy)
    have hxl : x ∈ s₁ :: s₂ :: s₃ :: rest := by
      rcases List.mem_cons.mp hx with rfl | hx3
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx3)
    have hyl : y ∈ s₁ :: s₂ :: s₃ :: rest := by
      rcases List.mem_cons.mp hy with rfl | hy3
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy3)
    have hd23 : DistOneIn (s₁ :: s₂ :: s₃ :: rest) s₂ s₃ :=
      distOneIn_cons_iff.mpr (Or.inr (Or.inr
        (distOneIn_cons_iff.mpr
          (Or.inl ⟨rfl, s₃, rest, rfl, rfl⟩))))
    have hd12 : DistOneIn (s₁ :: s₂ :: s₃ :: rest) s₁ s₂ :=
      distOneIn_cons_iff.mpr
        (Or.inl ⟨rfl, s₂, s₃ :: rest, rfl, rfl⟩)
    have hAdj12 : (gameGraph (patternGraph A) lS).Adj s₁ s₂ :=
      (hadj s₁ (by simp) s₂ (by simp) h12).mpr hd12
    have hAdj32 : (gameGraph (patternGraph A) lS).Adj s₃ s₂ :=
      (hadj s₃ (by simp) s₂ (by simp) (Ne.symm h23)).mpr
        (distOneIn_comm.mp hd23)
    rw [gameGraph_append_singleton, elimStep_adj_iff_of_ne hxy,
      hadj x hxl y hyl hxy]
    constructor
    · rintro (h | ⟨hxA, hyA⟩)
      · -- DistOne in old list, x y ≠ s₂ → DistOne in new list
        by_cases hx1 : x = s₁
        · subst hx1
          exact absurd (distOne_head hnd h) hy2
        by_cases hy1 : y = s₁
        · subst hy1
          exact absurd (distOne_head hnd (distOneIn_comm.mp h)) hx2
        · have h' : DistOneIn (s₃ :: rest) x y := by
            have step1 : DistOneIn (s₂ :: s₃ :: rest) x y := by
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
          exact distOneIn_cons_iff.mpr (Or.inr (Or.inr h'))
      · have hdx : x = s₁ ∨ x = s₃ :=
          fan_second_adj hstate0 hxl hx2 hxA.symm
        have hdy : y = s₁ ∨ y = s₃ :=
          fan_second_adj hstate0 hyl hy2 hyA.symm
        have hd13' : DistOneIn (s₁ :: s₃ :: rest) s₁ s₃ :=
          distOneIn_cons_iff.mpr
            (Or.inl ⟨rfl, s₃, rest, rfl, rfl⟩)
        rcases hdx with rfl | rfl <;> rcases hdy with rfl | rfl
        · exact absurd rfl hxy
        · exact hd13'
        · exact distOneIn_comm.mp hd13'
        · exact absurd rfl hxy
    · intro h
      by_cases hx1 : x = s₁
      · subst hx1
        have hy3 : y = s₃ := distOne_head hnd' h
        subst hy3
        exact Or.inr ⟨hAdj12, hAdj32⟩
      by_cases hy1 : y = s₁
      · subst hy1
        have hx3 : x = s₃ :=
          distOne_head hnd' (distOneIn_comm.mp h)
        subst hx3
        exact Or.inr ⟨hAdj32, hAdj12⟩
      · have h' : DistOneIn (s₃ :: rest) x y := by
          rw [distOneIn_cons_iff] at h
          rcases h with ⟨hxx, -⟩ | ⟨hyy, -⟩ | h
          · exact absurd hxx hx1
          · exact absurd hyy hy1
          · exact h
        exact Or.inl (distOneIn_cons_iff.mpr (Or.inr (Or.inr
          (distOneIn_cons_iff.mpr (Or.inr (Or.inr h'))))))




/-- The pivot update is symmetric in its two survivor indices. -/
theorem pivotEntry_comm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (S : Finset (Fin n))
    (p j k : Fin n) :
    pivotEntry A S p j k = pivotEntry A S p k j := by
  simp [pivotEntry, schurEntry_symm hA, mul_comm]



/-- A fan state with no path vertices: only the center remains. -/
theorem fan_continuation_nil {A : Matrix (Fin n) (Fin n) ℝ}
    {lS : List (Fin n)} {S : Finset (Fin n)}
    {c : Fin n} (hstate : IsFanState A lS S c []) :
    AdmitsCleanContinuation A lS S := by
  obtain ⟨henum, hcS, -, hmem, -, -⟩ := hstate
  refine ⟨henum, [c], by simp, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      simp only [List.mem_singleton] at hx
      rw [hx]
      exact hcS
    · intro hx
      have hxc : x = c := by
        by_contra hne
        exact absurd ((hmem x).mpr ⟨hx, hne⟩) (by simp)
      simp [hxc]
  · intro p x hAfter _
    have h2 := afterIn_length_ge hAfter
    simp at h2



/-- A fan state with one path vertex, in State 0. -/
theorem fan_continuation_single {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {lS : List (Fin n)}
    {S : Finset (Fin n)} {c s₁ : Fin n}
    (hstate : IsFanState A lS S c [s₁])
    (h0 : FanStateZero A S c [s₁]) :
    AdmitsCleanContinuation A lS S := by
  obtain ⟨henum, hcS, hnd, hmem, hcenter, -⟩ := hstate
  have hs₁S : s₁ ∉ S := ((hmem s₁).mp (by simp)).1
  have hs₁c : s₁ ≠ c := ((hmem s₁).mp (by simp)).2
  have hclean : ∀ x : Fin n, x ∉ S → x ≠ s₁ →
      (gameGraph (patternGraph A) lS).Adj s₁ x →
      schurEntry A S s₁ x ≠ 0 := by
    intro x hxS hx1 _
    have hxc : x = c := by
      by_contra hne
      have hxmem : x ∈ ([s₁] : List (Fin n)) :=
        (hmem x).mpr ⟨hxS, hne⟩
      simp only [List.mem_singleton] at hxmem
      exact hx1 hxmem
    rw [hxc, schurEntry_symm hA]
    exact h0.1 s₁ (by simp)
  refine admitsCleanContinuation_cons hs₁S hclean ?_
  refine fan_continuation_nil (c := c) ⟨enumerates_append_singleton henum
    hs₁S, ?_, by simp, ?_, by simp, by simp⟩
  · exact fun h => (Finset.mem_insert.mp h).elim
      (fun hh => hs₁c hh.symm) hcS
  · intro x
    constructor
    · simp
    · rintro ⟨hxS, hxc⟩
      have hxS' : x ∉ S :=
        fun h => hxS (Finset.mem_insert_of_mem h)
      have hxmem : x ∈ ([s₁] : List (Fin n)) :=
        (hmem x).mpr ⟨hxS', hxc⟩
      simp only [List.mem_singleton] at hxmem
      exact absurd (hxmem ▸ Finset.mem_insert_self s₁ S) hxS



/-- The fan state induction of paper Theorem 4.8 (i): every fan
state in State 0 or State 1 admits a clean continuation. -/
theorem fan_continuation {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∀ (m : ℕ) {lS : List (Fin n)} {S : Finset (Fin n)} {c : Fin n}
      {l : List (Fin n)}, l.length ≤ m → IsFanState A lS S c l →
      (FanStateZero A S c l ∨ FanStateOne A S c l) →
      AdmitsCleanContinuation A lS S := by
  intro m
  induction m with
  | zero =>
      intro lS S c l hlen hstate _hst
      have hl : l = [] :=
        List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst hl
      exact fan_continuation_nil hstate
  | succ m ih =>
    intro lS S c l hlen hstate hst
    cases l with
    | nil => exact fan_continuation_nil hstate
    | cons s₁ l' =>
      cases l' with
      | nil =>
        rcases hst with h0 | h1
        · exact fan_continuation_single hA hstate h0
        · obtain ⟨t₁, t₂, rest₁, hl, -, -, -⟩ := h1
          simp at hl
      | cons s₂ rest =>
        have hstate0 := hstate
        obtain ⟨henum, hcS, hnd, hmem, hcenter, hadj⟩ := hstate
        have hnot1 : s₁ ∉ s₂ :: rest := (List.nodup_cons.mp hnd).1
        have hnd2 : (s₂ :: rest).Nodup :=
          (List.nodup_cons.mp hnd).2
        have h12 : s₁ ≠ s₂ := fun hh => hnot1 (by simp [hh])
        have hs₁S : s₁ ∉ S := ((hmem s₁).mp (by simp)).1
        have hs₂S : s₂ ∉ S := ((hmem s₂).mp (by simp)).1
        have hs₁c : s₁ ≠ c := ((hmem s₁).mp (by simp)).2
        have hs₂c : s₂ ≠ c := ((hmem s₂).mp (by simp)).2
        have hc_out : c ∉ insert s₁ S := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨Ne.symm hs₁c, hcS⟩
        have hs₂out : s₂ ∉ insert s₁ S := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨Ne.symm h12, hs₂S⟩
        have hd12 : DistOneIn (s₁ :: s₂ :: rest) s₁ s₂ :=
          distOneIn_cons_iff.mpr
            (Or.inl ⟨rfl, s₂, rest, rfl, rfl⟩)
        have hlen' : (s₂ :: rest).length ≤ m := by
          simp only [List.length_cons] at hlen ⊢
          omega
        have hleg1 : ∀ z ∈ s₂ :: rest, z ≠ s₂ →
            schurEntry A S z s₁ = 0 := by
          intro z hz hz2
          have hz1 : z ≠ s₁ := fun hh => hnot1 (hh ▸ hz)
          refine schurEntry_eq_zero_of_not_gameAdj hA lS S henum
            (x := z) (y := s₁) hz1 ?_
          intro hAdj
          exact hz2 (fan_head_adj hstate0 (List.mem_cons_of_mem _ hz)
            hz1 hAdj.symm)
        have hout1 : ∀ x ∈ s₂ :: rest, x ∉ insert s₁ S := by
          intro x hx
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun hh => hnot1 (hh ▸ hx),
            ((hmem x).mp (List.mem_cons_of_mem _ hx)).1⟩
        have hFanTail0 :
            (∀ x ∈ s₂ :: rest, x ≠ s₂ → schurEntry A S c x ≠ 0) →
            (∀ x y, DistOneIn (s₁ :: s₂ :: rest) x y →
              schurEntry A S x y ≠ 0) →
            schurEntry A (insert s₁ S) c s₂ ≠ 0 →
            FanStateZero A (insert s₁ S) c (s₂ :: rest) := by
          intro hcenter' hpath hc2
          refine ⟨?_, ?_⟩
          · intro x hx
            by_cases hx2 : x = s₂
            · rw [hx2]
              exact hc2
            · rw [schurEntry_insert_eq_of_leg_zero hA S hs₁S hc_out
                (hout1 x hx) (Or.inr (hleg1 x hx hx2))]
              exact hcenter' x hx hx2
          · intro x y hdist
            have hxy : x ≠ y := distOneIn_ne hnd2 hdist
            have hx : x ∈ s₂ :: rest := (distOneIn_mem hdist).1
            have hy : y ∈ s₂ :: rest := (distOneIn_mem hdist).2
            have hleg : schurEntry A S x s₁ = 0
                ∨ schurEntry A S y s₁ = 0 := by
              by_cases hx2 : x = s₂
              · exact Or.inr
                  (hleg1 y hy (fun hh => hxy (hx2.trans hh.symm)))
              · exact Or.inl (hleg1 x hx hx2)
            rw [schurEntry_insert_eq_of_leg_zero hA S hs₁S
              (hout1 x hx) (hout1 y hy) hleg]
            exact hpath x y
              (distOneIn_cons_iff.mpr (Or.inr (Or.inr hdist)))
        have hneighbors₁ : ∀ x : Fin n, x ∉ S → x ≠ s₁ →
            (gameGraph (patternGraph A) lS).Adj s₁ x →
            x = c ∨ x = s₂ := by
          intro x hxS hx1 hAdj
          by_cases hxc : x = c
          · exact Or.inl hxc
          · exact Or.inr (fan_head_adj hstate0 ((hmem x).mpr
              ⟨hxS, hxc⟩) hx1 hAdj)
        rcases hst with h0 | h1
        · -- State 0
          have hclean₁ : ∀ x : Fin n, x ∉ S → x ≠ s₁ →
              (gameGraph (patternGraph A) lS).Adj s₁ x →
              schurEntry A S s₁ x ≠ 0 := by
            intro x hxS hx1 hAdj
            rcases hneighbors₁ x hxS hx1 hAdj with rfl | hx2
            · rw [schurEntry_symm hA]
              exact h0.1 s₁ (by simp)
            · rw [hx2]
              exact h0.2 s₁ s₂ hd12
          by_cases hzero : schurEntry A (insert s₁ S) c s₂ = 0
          · cases rest with
            | nil =>
              -- triangle {c, s₁, s₂}: pivot s₂ by exchange
              have hpe : pivotEntry A S s₁ s₂ c = 0 := by
                have h2 : pivotEntry A S s₁ c s₂ = 0 := by
                  rw [← schur_quotient hA S s₁ hs₁S c s₂ hc_out
                    hs₂out]
                  exact hzero
                rwa [← pivotEntry_comm hA S s₁ s₂ c] at h2
              have h1c : schurEntry A S s₁ c ≠ 0 := by
                rw [schurEntry_symm hA]
                exact h0.1 s₁ (by simp)
              have hpe2 : pivotEntry A S s₂ s₁ c ≠ 0 :=
                pivotEntry_ne_of_eq_zero hA S hs₁S hs₂S hcS h12 hs₁c hs₂c
                  h1c hpe
              have hs₁out2 : s₁ ∉ insert s₂ S := by
                simp only [Finset.mem_insert, not_or]
                exact ⟨h12, hs₁S⟩
              have hc_out2 : c ∉ insert s₂ S := by
                simp only [Finset.mem_insert, not_or]
                exact ⟨Ne.symm hs₂c, hcS⟩
              have hclean₂ : ∀ x : Fin n, x ∉ S → x ≠ s₂ →
                  (gameGraph (patternGraph A) lS).Adj s₂ x →
                  schurEntry A S s₂ x ≠ 0 := by
                intro x hxS hx2 _
                by_cases hxc : x = c
                · rw [hxc, schurEntry_symm hA]
                  exact h0.1 s₂ (by simp)
                · have hxl : x ∈ s₁ :: s₂ :: [] :=
                    (hmem x).mpr ⟨hxS, hxc⟩
                  simp only [List.mem_cons, List.not_mem_nil,
                    or_false] at hxl
                  rcases hxl with hx1 | hx2'
                  · rw [hx1]
                    exact h0.2 s₂ s₁ (distOneIn_comm.mp hd12)
                  · exact absurd hx2' hx2
              refine admitsCleanContinuation_cons hs₂S hclean₂ ?_
              refine admitsCleanContinuation_two
                (enumerates_append_singleton henum hs₂S)
                hs₁out2 hc_out2 hs₁c ?_ ?_
              · intro x hx
                have hxS : x ∉ S :=
                  fun h => hx (Finset.mem_insert_of_mem h)
                have hx2 : x ≠ s₂ :=
                  fun hh => hx (hh ▸ Finset.mem_insert_self s₂ S)
                by_cases hxc : x = c
                · exact Or.inr hxc
                · have hxl : x ∈ s₁ :: s₂ :: [] :=
                    (hmem x).mpr ⟨hxS, hxc⟩
                  simp only [List.mem_cons, List.not_mem_nil,
                    or_false] at hxl
                  rcases hxl with rfl | rfl
                  · exact Or.inl rfl
                  · exact absurd rfl hx2
              · intro _
                rw [schur_quotient hA S s₂ hs₂S s₁ c hs₁out2
                  hc_out2]
                exact hpe2
            | cons s₃ rest' =>
              -- SECOND at s₂
              have hnot2 : s₂ ∉ s₃ :: rest' :=
                (List.nodup_cons.mp hnd2).1
              have hnd3 : (s₃ :: rest').Nodup :=
                (List.nodup_cons.mp hnd2).2
              have h13 : s₁ ≠ s₃ := fun hh => hnot1 (by simp [hh])
              have h23 : s₂ ≠ s₃ := fun hh => hnot2 (by simp [hh])
              have hs₃S : s₃ ∉ S := ((hmem s₃).mp (by simp)).1
              have hs₁out2 : s₁ ∉ insert s₂ S := by
                simp only [Finset.mem_insert, not_or]
                exact ⟨h12, hs₁S⟩
              have hs₃out2 : s₃ ∉ insert s₂ S := by
                simp only [Finset.mem_insert, not_or]
                exact ⟨Ne.symm h23, hs₃S⟩
              have hc_out2 : c ∉ insert s₂ S := by
                simp only [Finset.mem_insert, not_or]
                exact ⟨Ne.symm hs₂c, hcS⟩
              have hd23 : DistOneIn (s₁ :: s₂ :: s₃ :: rest') s₂ s₃ :=
                distOneIn_cons_iff.mpr (Or.inr (Or.inr
                  (distOneIn_cons_iff.mpr
                    (Or.inl ⟨rfl, s₃, rest', rfl, rfl⟩))))
              have hnd' : (s₁ :: s₃ :: rest').Nodup := by
                refine List.nodup_cons.mpr ⟨?_, hnd3⟩
                intro h
                exact hnot1 (List.mem_cons_of_mem _ h)
              have hpe : pivotEntry A S s₁ s₂ c = 0 := by
                have h2 : pivotEntry A S s₁ c s₂ = 0 := by
                  rw [← schur_quotient hA S s₁ hs₁S c s₂ hc_out
                    hs₂out]
                  exact hzero
                rwa [← pivotEntry_comm hA S s₁ s₂ c] at h2
              have e_c1 : schurEntry A (insert s₂ S) c s₁ ≠ 0 := by
                have h1c : schurEntry A S s₁ c ≠ 0 := by
                  rw [schurEntry_symm hA]
                  exact h0.1 s₁ (by simp)
                have h2 : pivotEntry A S s₂ s₁ c ≠ 0 :=
                  pivotEntry_ne_of_eq_zero hA S hs₁S hs₂S hcS h12 hs₁c hs₂c
                    h1c hpe
                rw [schur_quotient hA S s₂ hs₂S c s₁ hc_out2
                  hs₁out2, pivotEntry_comm hA S s₂ c s₁]
                exact h2
              have e13 : schurEntry A (insert s₂ S) s₁ s₃ ≠ 0 := by
                have hf := (fresh_fill A hA lS S henum s₂ s₁ s₃
                  hs₂S hs₁out2 hs₃out2 h13
                  ((hadj s₁ (by simp) s₂ (by simp) h12).mpr hd12)
                  ((hadj s₃ (by simp) s₂ (by simp)
                    (Ne.symm h23)).mpr (distOneIn_comm.mp hd23))
                  (fun hAdj => by
                    have h2 := (hadj s₁ (by simp) s₃ (by simp)
                      h13).mp hAdj
                    exact (Ne.symm h23) (distOne_head hnd h2))).2.2
                refine hf (h0.2 s₁ s₂ hd12) ?_
                rw [schurEntry_symm hA]
                exact h0.2 s₂ s₃ hd23
              have hnot2' : s₂ ∉ s₁ :: s₃ :: rest' := by
                intro h
                rcases List.mem_cons.mp h with hh | hh
                · exact (Ne.symm h12) hh
                · exact hnot2 hh
              have hleg2 : ∀ z ∈ s₁ :: s₃ :: rest', z ≠ s₁ → z ≠ s₃ →
                  schurEntry A S z s₂ = 0 := by
                intro z hz hz1 hz3
                have hz2 : z ≠ s₂ := fun hh => hnot2' (hh ▸ hz)
                have hzl : z ∈ s₁ :: s₂ :: s₃ :: rest' := by
                  rcases List.mem_cons.mp hz with rfl | hz3'
                  · simp
                  · exact List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ hz3')
                refine schurEntry_eq_zero_of_not_gameAdj hA lS S
                  henum (x := z) (y := s₂) hz2 ?_
                intro hAdj
                have := fan_second_adj hstate0 hzl hz2 hAdj.symm
                rcases this with hh | hh
                · exact hz1 hh
                · exact hz3 hh
              have hout2 : ∀ x ∈ s₁ :: s₃ :: rest',
                  x ∉ insert s₂ S := by
                intro x hx
                simp only [Finset.mem_insert, not_or]
                have hxl : x ∈ s₁ :: s₂ :: s₃ :: rest' := by
                  rcases List.mem_cons.mp hx with rfl | hx3
                  · simp
                  · exact List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ hx3)
                exact ⟨fun hh => hnot2' (hh ▸ hx),
                  ((hmem x).mp hxl).1⟩
              have hclean₂ : ∀ x : Fin n, x ∉ S → x ≠ s₂ →
                  (gameGraph (patternGraph A) lS).Adj s₂ x →
                  schurEntry A S s₂ x ≠ 0 := by
                intro x hxS hx2 hAdj
                by_cases hxc : x = c
                · rw [hxc, schurEntry_symm hA]
                  exact h0.1 s₂ (by simp)
                · have hxl : x ∈ s₁ :: s₂ :: s₃ :: rest' :=
                    (hmem x).mpr ⟨hxS, hxc⟩
                  rcases fan_second_adj hstate0 hxl hx2 hAdj with
                    hx1' | hx3'
                  · rw [hx1']
                    exact h0.2 s₂ s₁ (distOneIn_comm.mp hd12)
                  · rw [hx3']
                    exact h0.2 s₂ s₃ hd23
              refine admitsCleanContinuation_cons hs₂S hclean₂ ?_
              have hlen'' : (s₁ :: s₃ :: rest').length ≤ m := by
                simp only [List.length_cons] at hlen ⊢
                omega
              refine ih hlen'' (fanState_second hstate0) ?_
              have hcenter' : ∀ x ∈ s₁ :: s₃ :: rest', x ≠ s₃ →
                  schurEntry A (insert s₂ S) c x ≠ 0 := by
                intro x hx hx3
                by_cases hx1 : x = s₁
                · rw [hx1]
                  exact e_c1
                · rw [schurEntry_insert_eq_of_leg_zero hA S hs₂S
                    hc_out2 (hout2 x hx) (Or.inr (hleg2 x hx hx1 hx3))]
                  refine h0.1 x ?_
                  rcases List.mem_cons.mp hx with rfl | hx3'
                  · simp
                  · exact List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ hx3')
              have hpath' : ∀ x y : Fin n,
                  DistOneIn (s₁ :: s₃ :: rest') x y →
                  schurEntry A (insert s₂ S) x y ≠ 0 := by
                intro x y hdist
                have hxy : x ≠ y := distOneIn_ne hnd' hdist
                have hx : x ∈ s₁ :: s₃ :: rest' :=
                  (distOneIn_mem hdist).1
                have hy : y ∈ s₁ :: s₃ :: rest' :=
                  (distOneIn_mem hdist).2
                by_cases hpair : SamePair x y s₁ s₃
                · rcases hpair with ⟨hx1, hy3⟩ | ⟨hx3, hy1⟩
                  · rw [hx1, hy3]
                    exact e13
                  · rw [hx3, hy1, schurEntry_symm hA]
                    exact e13
                · have hout : (x ≠ s₁ ∧ x ≠ s₃) ∨ (y ≠ s₁ ∧ y ≠ s₃) := by
                    by_contra hcon
                    have hcx : x = s₁ ∨ x = s₃ := by
                      by_contra hn
                      push Not at hn
                      exact hcon (Or.inl hn)
                    have hcy : y = s₁ ∨ y = s₃ := by
                      by_contra hn
                      push Not at hn
                      exact hcon (Or.inr hn)
                    rcases hcx with rfl | rfl <;>
                      rcases hcy with rfl | rfl
                    · exact hxy rfl
                    · exact hpair (Or.inl ⟨rfl, rfl⟩)
                    · exact hpair (Or.inr ⟨rfl, rfl⟩)
                    · exact hxy rfl
                  have hleg : schurEntry A S x s₂ = 0
                      ∨ schurEntry A S y s₂ = 0 := by
                    rcases hout with ⟨h1, h3⟩ | ⟨h1, h3⟩
                    · exact Or.inl (hleg2 x hx h1 h3)
                    · exact Or.inr (hleg2 y hy h1 h3)
                  rw [schurEntry_insert_eq_of_leg_zero hA S hs₂S
                    (hout2 x hx) (hout2 y hy) hleg]
                  refine h0.2 x y ?_
                  by_cases hx1 : x = s₁
                  · have hy3 : y = s₃ := by
                      rw [hx1] at hdist
                      exact distOne_head hnd' hdist
                    exact absurd (Or.inl ⟨hx1, hy3⟩) hpair
                  by_cases hy1 : y = s₁
                  · have hx3 : x = s₃ := by
                      rw [hy1] at hdist
                      exact distOne_head hnd' (distOneIn_comm.mp hdist)
                    exact absurd (Or.inr ⟨hx3, hy1⟩) hpair
                  · have h' : DistOneIn (s₃ :: rest') x y := by
                      rw [distOneIn_cons_iff] at hdist
                      rcases hdist with ⟨hxx, -⟩ | ⟨hyy, -⟩ | h
                      · exact absurd hxx hx1
                      · exact absurd hyy hy1
                      · exact h
                    exact distOneIn_cons_iff.mpr (Or.inr (Or.inr
                      (distOneIn_cons_iff.mpr (Or.inr (Or.inr h')))))
              by_cases hc3z : schurEntry A (insert s₂ S) c s₃ = 0
              · exact Or.inr ⟨s₁, s₃, rest', rfl, hc3z, hcenter',
                  hpath'⟩
              · refine Or.inl ⟨fun x hx => ?_, hpath'⟩
                by_cases hx3 : x = s₃
                · rw [hx3]
                  exact hc3z
                · exact hcenter' x hx hx3
          · refine admitsCleanContinuation_cons hs₁S hclean₁ ?_
            refine ih hlen' (fanState_end hstate0) (Or.inl ?_)
            exact hFanTail0
              (fun x hx _ => h0.1 x (List.mem_cons_of_mem _ hx))
              h0.2 hzero
        · -- State 1: END refills the exceptional center edge
          obtain ⟨t₁, t₂, rest₁, hl, hzero1, hcenter1, hpath1⟩ := h1
          have ht2 : t₂ = s₂ :=
            (List.cons.inj (List.cons.inj hl).2).1.symm
          rw [ht2] at hzero1 hcenter1
          have hclean₁ : ∀ x : Fin n, x ∉ S → x ≠ s₁ →
              (gameGraph (patternGraph A) lS).Adj s₁ x →
              schurEntry A S s₁ x ≠ 0 := by
            intro x hxS hx1 hAdj
            rcases hneighbors₁ x hxS hx1 hAdj with rfl | hx2
            · rw [schurEntry_symm hA]
              exact hcenter1 s₁ (by simp) h12
            · rw [hx2]
              exact hpath1 s₁ s₂ hd12
          have hrefill : schurEntry A (insert s₁ S) c s₂ ≠ 0 := by
            have hc1 : schurEntry A S c s₁ ≠ 0 :=
              hcenter1 s₁ (by simp) h12
            have h21 : schurEntry A S s₂ s₁ ≠ 0 := by
              rw [schurEntry_symm hA]
              exact hpath1 s₁ s₂ hd12
            have h11 : schurEntry A S s₁ s₁ ≠ 0 :=
              ne_of_gt (schurEntry_pos hA S hs₁S)
            rw [schur_quotient hA S s₁ hs₁S c s₂ hc_out hs₂out]
            have hval : pivotEntry A S s₁ c s₂
                = - (schurEntry A S c s₁ * schurEntry A S s₂ s₁
                    / schurEntry A S s₁ s₁) := by
              simp [pivotEntry, hzero1]
            rw [hval]
            exact neg_ne_zero.mpr
              (div_ne_zero (mul_ne_zero hc1 h21) h11)
          refine admitsCleanContinuation_cons hs₁S hclean₁ ?_
          refine ih hlen' (fanState_end hstate0) (Or.inl ?_)
          exact hFanTail0
            (fun x hx hx2 => hcenter1 x (List.mem_cons_of_mem _ hx)
              hx2) hpath1 hrefill



/-- Paper Theorem 4.8 (i), fans: dominating-vertex fans admit
per-matrix clean orderings (the per-matrix form; not the paper's
strategy form). -/
theorem fans_perMatrix {G : SimpleGraph (Fin n)}
    (hG : IsFanPattern G) : PatternAdmitsPerMatrixCleanOrdering G := by
  intro A hA hpat
  obtain ⟨c, l, hnd, hmeml, hcenterG, hadjG⟩ := hG
  apply exists_clean_of_continuation_empty hA
  refine fan_continuation (c := c) hA l.length le_rfl
    ⟨⟨by simp, by simp⟩, by simp, hnd, ?_, ?_, ?_⟩
    (Or.inl ⟨?_, ?_⟩)
  · intro x
    exact ⟨fun h => ⟨Finset.notMem_empty x, (hmeml x).mp h⟩,
      fun h => (hmeml x).mpr h.2⟩
  · intro x hx
    exact hpat.symm ▸ hcenterG x ((hmeml x).mp hx)
  · intro x hx y hy _
    have hgg : gameGraph (patternGraph A) ([] : List (Fin n))
        = patternGraph A := rfl
    rw [hgg, hpat]
    exact hadjG x y ((hmeml x).mp hx) ((hmeml y).mp hy)
  · intro x hx
    rw [schurEntry_empty]
    exact patternGraph_adj_entry hA
      (hpat.symm ▸ hcenterG x ((hmeml x).mp hx))
  · intro x y hdist
    rw [schurEntry_empty]
    have hx : x ∈ l := (distOneIn_mem hdist).1
    have hy : y ∈ l := (distOneIn_mem hdist).2
    exact patternGraph_adj_entry hA
      (hpat.symm ▸ (hadjG x y ((hmeml x).mp hx)
        ((hmeml y).mp hy)).mpr hdist)

end CholeskyCancellations

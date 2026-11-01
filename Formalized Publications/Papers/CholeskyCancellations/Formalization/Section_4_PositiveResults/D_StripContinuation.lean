/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.TakeWhile
import Section_4_PositiveResults.C_StripHelpers

/-! # Strip continuation (paper Section 4)

The strip state machine (`strip_continuation`) and the per-matrix strip class theorem (`strips_perMatrix`, Theorem 4.8). Split from `Positives.lean`.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as `Defs.lean`; graph classes are predicates on `SimpleGraph (Fin n)` patterns and cleanliness is quantified per SPD realization through `PatternAdmitsPerMatrixCleanOrdering`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}



theorem distOneIn_ne {l : List (Fin n)} (hnd : l.Nodup) {x y : Fin n}
    (h : DistOneIn l x y) : x ≠ y := by
  rintro rfl
  rcases h with ⟨l₁, l₂, rfl⟩ | ⟨l₁, l₂, rfl⟩ <;>
    exact (List.nodup_cons.mp
      (List.nodup_append.mp hnd).2.1).1 (by simp)



theorem distTwoIn_ne {l : List (Fin n)} (hnd : l.Nodup) {x y : Fin n}
    (h : DistTwoIn l x y) : x ≠ y := by
  rintro rfl
  rcases h with ⟨l₁, l₂, z, rfl⟩ | ⟨l₁, l₂, z, rfl⟩ <;>
    exact (List.nodup_cons.mp
      (List.nodup_append.mp hnd).2.1).1 (by simp)



/-- The strip state induction of paper Theorem 4.8 (i): every strip
state in State 0 or State 1 admits a clean continuation. -/
theorem strip_continuation {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∀ (m : ℕ) {lS : List (Fin n)} {S : Finset (Fin n)}
      {l : List (Fin n)}, l.length ≤ m → IsStripState A lS S l →
      (StripStateZero A S l ∨ StripStateOne A S l) →
      AdmitsCleanContinuation A lS S := by
  intro m
  induction m with
  | zero =>
      intro lS S l hlen hstate hst
      have hl : l = [] :=
        List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst hl
      exact strip_continuation_small (by simp) hstate hst
  | succ m ih =>
    intro lS S l hlen hstate hst
    by_cases hsmall : l.length ≤ 2
    · exact strip_continuation_small hsmall hstate hst
    obtain ⟨s₁, s₂, s₃, rest, rfl⟩ :
        ∃ s₁ s₂ s₃ rest, l = s₁ :: s₂ :: s₃ :: rest := by
      cases l with
      | nil => simp at hsmall
      | cons a l =>
        cases l with
        | nil => simp at hsmall
        | cons b l =>
          cases l with
          | nil => simp at hsmall
          | cons c l => exact ⟨a, b, c, l, rfl⟩
    have hstate0 := hstate
    obtain ⟨henum, hnd, hmem, hadj⟩ := hstate
    have hnot1 : s₁ ∉ s₂ :: s₃ :: rest := (List.nodup_cons.mp hnd).1
    have hnd2 : (s₂ :: s₃ :: rest).Nodup :=
      (List.nodup_cons.mp hnd).2
    have hnot2 : s₂ ∉ s₃ :: rest := (List.nodup_cons.mp hnd2).1
    have h12 : s₁ ≠ s₂ := fun hh => hnot1 (by simp [hh])
    have h13 : s₁ ≠ s₃ := fun hh => hnot1 (by simp [hh])
    have h23 : s₂ ≠ s₃ := fun hh => hnot2 (by simp [hh])
    have hs₁S : s₁ ∉ S := (hmem s₁).mp (by simp)
    have hs₂S : s₂ ∉ S := (hmem s₂).mp (by simp)
    have hs₃S : s₃ ∉ S := (hmem s₃).mp (by simp)
    have hs₂out : s₂ ∉ insert s₁ S := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨Ne.symm h12, hs₂S⟩
    have hs₃out : s₃ ∉ insert s₁ S := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨Ne.symm h13, hs₃S⟩
    have hd12 : DistOneIn (s₁ :: s₂ :: s₃ :: rest) s₁ s₂ :=
      distOneIn_cons_iff.mpr
        (Or.inl ⟨rfl, s₂, s₃ :: rest, rfl, rfl⟩)
    have hd13 : DistTwoIn (s₁ :: s₂ :: s₃ :: rest) s₁ s₃ :=
      distTwoIn_cons_iff.mpr
        (Or.inl ⟨rfl, s₂, s₃, rest, rfl, rfl⟩)
    have hlen' : (s₂ :: s₃ :: rest).length ≤ m := by
      simp only [List.length_cons] at hlen ⊢
      omega
    -- END pivot at s₁ is clean in both states
    have hclean₁ : ∀ x : Fin n, x ∉ S → x ≠ s₁ →
        (gameGraph (patternGraph A) lS).Adj s₁ x →
        schurEntry A S s₁ x ≠ 0 := by
      intro x hxS hx1 hAdj
      have hxl : x ∈ s₁ :: s₂ :: s₃ :: rest := (hmem x).mpr hxS
      have hx23 := strip_head_adj hstate0 hxl hx1 hAdj
      rcases hst with h0 | h1
      · rcases hx23 with hx2 | hx3
        · rw [hx2]
          exact h0 s₁ s₂ (Or.inl hd12)
        · rw [hx3]
          exact h0 s₁ s₃ (Or.inr hd13)
      · obtain ⟨t₁, t₂, t₃, rest₁, hl, -, hne1⟩ := h1
        have ht2 : t₂ = s₂ :=
          (List.cons.inj (List.cons.inj hl).2).1.symm
        have ht3 : t₃ = s₃ :=
          (List.cons.inj (List.cons.inj (List.cons.inj hl).2).2).1.symm
        rw [ht2, ht3] at hne1
        rcases hx23 with hx2 | hx3
        · rw [hx2]
          refine hne1 s₁ s₂ (Or.inl hd12) ?_
          rintro (⟨hh, -⟩ | ⟨hh, -⟩)
          · exact h12 hh
          · exact h13 hh
        · rw [hx3]
          refine hne1 s₁ s₃ (Or.inr hd13) ?_
          rintro (⟨hh, -⟩ | ⟨hh, -⟩)
          · exact h12 hh
          · exact h13 hh
    -- END: the tail is in State 0 provided the (s₂, s₃) entry after
    -- the pivot is nonzero and all other old pair entries are.
    have hTail0 : (∀ x y : Fin n,
          (DistOneIn (s₁ :: s₂ :: s₃ :: rest) x y
            ∨ DistTwoIn (s₁ :: s₂ :: s₃ :: rest) x y) →
          ¬ SamePair x y s₂ s₃ → schurEntry A S x y ≠ 0) →
        schurEntry A (insert s₁ S) s₂ s₃ ≠ 0 →
        StripStateZero A (insert s₁ S) (s₂ :: s₃ :: rest) := by
      intro hold h23ne x y hdist
      have hxy : x ≠ y := by
        rcases hdist with h | h
        · exact distOneIn_ne hnd2 h
        · exact distTwoIn_ne hnd2 h
      have hx : x ∈ s₂ :: s₃ :: rest := by
        rcases hdist with h | h
        · exact (distOneIn_mem h).1
        · exact (distTwoIn_mem h).1
      have hy : y ∈ s₂ :: s₃ :: rest := by
        rcases hdist with h | h
        · exact (distOneIn_mem h).2
        · exact (distTwoIn_mem h).2
      by_cases hpair : SamePair x y s₂ s₃
      · rcases hpair with ⟨hx2, hy3⟩ | ⟨hx3, hy2⟩
        · rw [hx2, hy3]
          exact h23ne
        · rw [hx3, hy2, schurEntry_symm hA]
          exact h23ne
      · rw [strip_entry_end_of_ne hA hstate0 hx hy hxy hpair]
        apply hold
        · have hx1 : x ≠ s₁ := fun hh => hnot1 (hh ▸ hx)
          have hy1 : y ≠ s₁ := fun hh => hnot1 (hh ▸ hy)
          exact (dist_cons_tail_iff hx1 hy1).mpr hdist
        · exact hpair
    rcases hst with h0 | h1
    · -- State 0
      by_cases hrest : rest = []
      · subst hrest
        by_cases hpe : pivotEntry A S s₁ s₂ s₃ = 0
        · -- three survivors, apex s₂ is clean by the exchange step
          have hd23 : DistOneIn (s₁ :: s₂ :: s₃ :: []) s₂ s₃ :=
            distOneIn_cons_iff.mpr (Or.inr (Or.inr
              (distOneIn_cons_iff.mpr
                (Or.inl ⟨rfl, s₃, [], rfl, rfl⟩))))
          have hpe2 : pivotEntry A S s₂ s₁ s₃ ≠ 0 :=
            pivotEntry_ne_of_eq_zero hA S hs₁S hs₂S hs₃S h12 h13 h23
              (h0 s₁ s₃ (Or.inr hd13)) hpe
          have hclean₂ : ∀ x : Fin n, x ∉ S → x ≠ s₂ →
              (gameGraph (patternGraph A) lS).Adj s₂ x →
              schurEntry A S s₂ x ≠ 0 := by
            intro x hxS hx2 hAdj
            have hxl : x ∈ s₁ :: s₂ :: s₃ :: [] := (hmem x).mpr hxS
            have hdist := (hadj s₂ (by simp) x hxl
              (Ne.symm hx2)).mp hAdj
            have hx13 : x = s₁ ∨ x = s₃ := by
              rcases hdist with h | h
              · rw [distOneIn_cons_iff] at h
                rcases h with ⟨hh, -⟩ | ⟨hh, w, r, hl, hw⟩ | h
                · exact absurd hh (Ne.symm h12)
                · exact Or.inl hh
                · exact Or.inr (distOne_head hnd2 h)
              · rw [distTwoIn_cons_iff] at h
                rcases h with ⟨hh, -⟩ | ⟨hh, a, b, r, hl, hw⟩ | h
                · exact absurd hh (Ne.symm h12)
                · have hb : b = s₃ :=
                    (List.cons.inj (List.cons.inj hl).2).1.symm
                  exact absurd (hw.trans hb) h23
                · rw [distTwoIn_cons_iff] at h
                  rcases h with ⟨-, a, b, r, hl, -⟩ | ⟨hh, -⟩ | h
                  · have hlen2 := congrArg List.length hl
                    simp only [List.length_cons, List.length_nil]
                      at hlen2
                    omega
                  · exact absurd hh hx2
                  · exact absurd (distTwoIn_mem h).1 (by simp [h23])
            rcases hx13 with hx1' | hx3'
            · rw [hx1']
              exact h0 s₂ s₁ (Or.inl (distOneIn_comm.mp hd12))
            · rw [hx3']
              exact h0 s₂ s₃ (Or.inl hd23)
          have hs₁out2 : s₁ ∉ insert s₂ S := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨h12, hs₁S⟩
          have hs₃out2 : s₃ ∉ insert s₂ S := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨Ne.symm h23, hs₃S⟩
          refine admitsCleanContinuation_cons hs₂S hclean₂ ?_
          refine admitsCleanContinuation_two
            (enumerates_append_singleton henum hs₂S)
            hs₁out2 hs₃out2 h13 ?_ ?_
          · intro x hx
            have hxS : x ∉ S :=
              fun h => hx (Finset.mem_insert_of_mem h)
            have hx2 : x ≠ s₂ :=
              fun hh => hx (hh ▸ Finset.mem_insert_self s₂ S)
            have hxl : x ∈ s₁ :: s₂ :: s₃ :: [] :=
              (hmem x).mpr hxS
            simp only [List.mem_cons, List.not_mem_nil, or_false]
              at hxl
            rcases hxl with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact absurd rfl hx2
            · exact Or.inr rfl
          · intro _
            rw [schur_quotient hA S s₂ hs₂S s₁ s₃ hs₁out2 hs₃out2]
            exact hpe2
        · -- three survivors, apex s₁ is clean: END
          refine admitsCleanContinuation_cons hs₁S hclean₁ ?_
          refine admitsCleanContinuation_two
            (enumerates_append_singleton henum hs₁S)
            hs₂out hs₃out h23 ?_ ?_
          · intro x hx
            have hxS : x ∉ S :=
              fun h => hx (Finset.mem_insert_of_mem h)
            have hx1 : x ≠ s₁ :=
              fun hh => hx (hh ▸ Finset.mem_insert_self s₁ S)
            have hxl : x ∈ s₁ :: s₂ :: s₃ :: [] :=
              (hmem x).mpr hxS
            simp only [List.mem_cons, List.not_mem_nil, or_false]
              at hxl
            rcases hxl with rfl | rfl | rfl
            · exact absurd rfl hx1
            · exact Or.inl rfl
            · exact Or.inr rfl
          · intro _
            rw [schur_quotient hA S s₁ hs₁S s₂ s₃ hs₂out hs₃out]
            exact hpe
      · -- State 0, at least four survivors
        obtain ⟨s₄, rest', rfl⟩ : ∃ s₄ rest', rest = s₄ :: rest' := by
          cases rest with
          | nil => exact absurd rfl hrest
          | cons a r => exact ⟨a, r, rfl⟩
        have hnd3 : (s₃ :: s₄ :: rest').Nodup :=
          (List.nodup_cons.mp hnd2).2
        have hnot3 : s₃ ∉ s₄ :: rest' := (List.nodup_cons.mp hnd3).1
        have h14 : s₁ ≠ s₄ := fun hh => hnot1 (by simp [hh])
        have h24 : s₂ ≠ s₄ := fun hh => hnot2 (by simp [hh])
        have h34 : s₃ ≠ s₄ := fun hh => hnot3 (by simp [hh])
        have hs₄S : s₄ ∉ S := (hmem s₄).mp (by simp)
        have hnd' : (s₁ :: s₃ :: s₄ :: rest').Nodup := by
          refine List.nodup_cons.mpr ⟨?_, hnd3⟩
          intro h
          exact hnot1 (List.mem_cons_of_mem _ h)
        have hd23 : DistOneIn (s₁ :: s₂ :: s₃ :: s₄ :: rest') s₂ s₃ :=
          distOneIn_cons_iff.mpr (Or.inr (Or.inr
            (distOneIn_cons_iff.mpr
              (Or.inl ⟨rfl, s₃, s₄ :: rest', rfl, rfl⟩))))
        have hd24 : DistTwoIn (s₁ :: s₂ :: s₃ :: s₄ :: rest') s₂ s₄ :=
          distTwoIn_cons_iff.mpr (Or.inr (Or.inr
            (distTwoIn_cons_iff.mpr
              (Or.inl ⟨rfl, s₃, s₄, rest', rfl, rfl⟩))))
        by_cases hzero : schurEntry A (insert s₁ S) s₂ s₃ = 0
        · -- SECOND at s₂
          have hs₁out2 : s₁ ∉ insert s₂ S := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨h12, hs₁S⟩
          have hs₃out2 : s₃ ∉ insert s₂ S := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨Ne.symm h23, hs₃S⟩
          have hs₄out2 : s₄ ∉ insert s₂ S := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨Ne.symm h24, hs₄S⟩
          have hpe : pivotEntry A S s₁ s₂ s₃ = 0 := by
            rw [← schur_quotient hA S s₁ hs₁S s₂ s₃ hs₂out hs₃out]
            exact hzero
          have e13 : schurEntry A (insert s₂ S) s₁ s₃ ≠ 0 := by
            rw [schur_quotient hA S s₂ hs₂S s₁ s₃ hs₁out2 hs₃out2]
            exact pivotEntry_ne_of_eq_zero hA S hs₁S hs₂S hs₃S h12 h13 h23
              (h0 s₁ s₃ (Or.inr hd13)) hpe
          have e14 : schurEntry A (insert s₂ S) s₁ s₄ ≠ 0 := by
            have hf := (fresh_fill A hA lS S henum s₂ s₁ s₄ hs₂S
              hs₁out2 hs₄out2 h14
              ((hadj s₁ (by simp) s₂ (by simp) h12).mpr
                (Or.inl hd12))
              ((hadj s₄ (by simp) s₂ (by simp) (Ne.symm h24)).mpr
                (Or.inr (distTwoIn_comm.mp hd24)))
              (fun hAdj => by
                have h2 := strip_head_adj hstate0 (by simp)
                  (Ne.symm h14) hAdj
                rcases h2 with hh | hh
                · exact (Ne.symm h24) hh
                · exact (Ne.symm h34) hh)).2.2
            refine hf (h0 s₁ s₂ (Or.inl hd12)) ?_
            rw [schurEntry_symm hA]
            exact h0 s₂ s₄ (Or.inr hd24)
          have hclean₂ : ∀ x : Fin n, x ∉ S → x ≠ s₂ →
              (gameGraph (patternGraph A) lS).Adj s₂ x →
              schurEntry A S s₂ x ≠ 0 := by
            intro x hxS hx2 hAdj
            have hxl : x ∈ s₁ :: s₂ :: s₃ :: s₄ :: rest' :=
              (hmem x).mpr hxS
            have hx134 := strip_second_adj hstate0 hxl hx2 hAdj
            rcases hx134 with hx1' | hx3' | hx4'
            · rw [hx1']
              exact h0 s₂ s₁ (Or.inl (distOneIn_comm.mp hd12))
            · rw [hx3']
              exact h0 s₂ s₃ (Or.inl hd23)
            · rw [hx4']
              exact h0 s₂ s₄ (Or.inr hd24)
          refine admitsCleanContinuation_cons hs₂S hclean₂ ?_
          have hlen'' : (s₁ :: s₃ :: s₄ :: rest').length ≤ m := by
            simp only [List.length_cons] at hlen ⊢
            omega
          refine ih hlen'' (stripState_second hstate0) ?_
          have hcommon : ∀ x y : Fin n,
              (DistOneIn (s₁ :: s₃ :: s₄ :: rest') x y
                ∨ DistTwoIn (s₁ :: s₃ :: s₄ :: rest') x y) →
              ¬ SamePair x y s₃ s₄ →
              schurEntry A (insert s₂ S) x y ≠ 0 := by
            intro x y hdist hns34
            have hxy : x ≠ y := by
              rcases hdist with h | h
              · exact distOneIn_ne hnd' h
              · exact distTwoIn_ne hnd' h
            have hx : x ∈ s₁ :: s₃ :: s₄ :: rest' := by
              rcases hdist with h | h
              · exact (distOneIn_mem h).1
              · exact (distTwoIn_mem h).1
            have hy : y ∈ s₁ :: s₃ :: s₄ :: rest' := by
              rcases hdist with h | h
              · exact (distOneIn_mem h).2
              · exact (distTwoIn_mem h).2
            by_cases h13p : SamePair x y s₁ s₃
            · rcases h13p with ⟨hx1, hy3⟩ | ⟨hx3, hy1⟩
              · rw [hx1, hy3]
                exact e13
              · rw [hx3, hy1, schurEntry_symm hA]
                exact e13
            by_cases h14p : SamePair x y s₁ s₄
            · rcases h14p with ⟨hx1, hy4⟩ | ⟨hx4, hy1⟩
              · rw [hx1, hy4]
                exact e14
              · rw [hx4, hy1, schurEntry_symm hA]
                exact e14
            · have hout : (x ≠ s₁ ∧ x ≠ s₃ ∧ x ≠ s₄)
                  ∨ (y ≠ s₁ ∧ y ≠ s₃ ∧ y ≠ s₄) := by
                by_contra hcon
                have hcx : x = s₁ ∨ x = s₃ ∨ x = s₄ := by
                  by_contra hn
                  push Not at hn
                  exact hcon (Or.inl hn)
                have hcy : y = s₁ ∨ y = s₃ ∨ y = s₄ := by
                  by_contra hn
                  push Not at hn
                  exact hcon (Or.inr hn)
                rcases hcx with rfl | rfl | rfl <;>
                  rcases hcy with rfl | rfl | rfl
                · exact hxy rfl
                · exact h13p (Or.inl ⟨rfl, rfl⟩)
                · exact h14p (Or.inl ⟨rfl, rfl⟩)
                · exact h13p (Or.inr ⟨rfl, rfl⟩)
                · exact hxy rfl
                · exact hns34 (Or.inl ⟨rfl, rfl⟩)
                · exact h14p (Or.inr ⟨rfl, rfl⟩)
                · exact hns34 (Or.inr ⟨rfl, rfl⟩)
                · exact hxy rfl
              rw [strip_entry_second_eq hA hstate0 hx hy hxy hout]
              apply h0
              rcases hdist with h | h
              · by_cases hx1 : x = s₁
                · have hy3 : y = s₃ := by
                    rw [hx1] at h
                    exact distOne_head hnd' h
                  exact absurd (Or.inl ⟨hx1, hy3⟩) h13p
                by_cases hy1 : y = s₁
                · have hx3 : x = s₃ := by
                    rw [hy1] at h
                    exact distOne_head hnd' (distOneIn_comm.mp h)
                  exact absurd (Or.inr ⟨hx3, hy1⟩) h13p
                · have h' : DistOneIn (s₃ :: s₄ :: rest') x y := by
                    rw [distOneIn_cons_iff] at h
                    rcases h with ⟨hxx, -⟩ | ⟨hyy, -⟩ | h
                    · exact absurd hxx hx1
                    · exact absurd hyy hy1
                    · exact h
                  exact Or.inl (distOneIn_cons_iff.mpr
                    (Or.inr (Or.inr (distOneIn_cons_iff.mpr
                      (Or.inr (Or.inr h'))))))
              · by_cases hx1 : x = s₁
                · have hy4 : y = s₄ := by
                    rw [hx1] at h
                    exact distTwo_head hnd' h
                  exact absurd (Or.inl ⟨hx1, hy4⟩) h14p
                by_cases hy1 : y = s₁
                · have hx4 : x = s₄ := by
                    rw [hy1] at h
                    exact distTwo_head hnd' (distTwoIn_comm.mp h)
                  exact absurd (Or.inr ⟨hx4, hy1⟩) h14p
                · have h' : DistTwoIn (s₃ :: s₄ :: rest') x y := by
                    rw [distTwoIn_cons_iff] at h
                    rcases h with ⟨hxx, -⟩ | ⟨hyy, -⟩ | h
                    · exact absurd hxx hx1
                    · exact absurd hyy hy1
                    · exact h
                  exact Or.inr (distTwoIn_cons_iff.mpr
                    (Or.inr (Or.inr (distTwoIn_cons_iff.mpr
                      (Or.inr (Or.inr h'))))))
          by_cases h34z : schurEntry A (insert s₂ S) s₃ s₄ = 0
          · exact Or.inr ⟨s₁, s₃, s₄, rest', rfl, h34z, hcommon⟩
          · refine Or.inl (fun x y hdist => ?_)
            by_cases hns : SamePair x y s₃ s₄
            · rcases hns with ⟨hx3, hy4⟩ | ⟨hx4, hy3⟩
              · rw [hx3, hy4]
                exact h34z
              · rw [hx4, hy3, schurEntry_symm hA]
                exact h34z
            · exact hcommon x y hdist hns
        · -- END with State-0 tail
          refine admitsCleanContinuation_cons hs₁S hclean₁ ?_
          refine ih hlen' (stripState_end hstate0) (Or.inl ?_)
          exact hTail0 (fun x y hd _ => h0 x y hd) hzero
    · -- State 1: END refills the exceptional zero
      obtain ⟨t₁, t₂, t₃, rest₁, hl, hzero, hne1⟩ := h1
      have ht2 : t₂ = s₂ :=
        (List.cons.inj (List.cons.inj hl).2).1.symm
      have ht3 : t₃ = s₃ :=
        (List.cons.inj (List.cons.inj (List.cons.inj hl).2).2).1.symm
      rw [ht2, ht3] at hzero hne1
      have hns12 : ¬ SamePair s₁ s₂ s₂ s₃ := by
        rintro (⟨hh, -⟩ | ⟨hh, -⟩)
        · exact h12 hh
        · exact h13 hh
      have hns13 : ¬ SamePair s₁ s₃ s₂ s₃ := by
        rintro (⟨hh, -⟩ | ⟨hh, -⟩)
        · exact h12 hh
        · exact h13 hh
      have hrefill : schurEntry A (insert s₁ S) s₂ s₃ ≠ 0 := by
        have h21 : schurEntry A S s₂ s₁ ≠ 0 := by
          rw [schurEntry_symm hA]
          exact hne1 s₁ s₂ (Or.inl hd12) hns12
        have h31 : schurEntry A S s₃ s₁ ≠ 0 := by
          rw [schurEntry_symm hA]
          exact hne1 s₁ s₃ (Or.inr hd13) hns13
        have h11 : schurEntry A S s₁ s₁ ≠ 0 :=
          ne_of_gt (schurEntry_pos hA S hs₁S)
        rw [schur_quotient hA S s₁ hs₁S s₂ s₃ hs₂out hs₃out]
        have hval : pivotEntry A S s₁ s₂ s₃
            = - (schurEntry A S s₂ s₁ * schurEntry A S s₃ s₁
                / schurEntry A S s₁ s₁) := by
          simp [pivotEntry, hzero]
        rw [hval]
        exact neg_ne_zero.mpr
          (div_ne_zero (mul_ne_zero h21 h31) h11)
      refine admitsCleanContinuation_cons hs₁S hclean₁ ?_
      refine ih hlen' (stripState_end hstate0) (Or.inl ?_)
      exact hTail0 hne1 hrefill




/-- Paper Theorem 4.8 (i), strips: 2-path strips admit per-matrix
clean orderings (the per-matrix form; not the paper's strategy
form). -/
theorem strips_perMatrix {G : SimpleGraph (Fin n)}
    (hG : IsStripPattern G) : PatternAdmitsPerMatrixCleanOrdering G := by
  intro A hA hpat
  obtain ⟨-, l, hord, hadjG⟩ := hG
  apply exists_clean_of_continuation_empty hA
  refine strip_continuation hA l.length le_rfl
    ⟨⟨by simp, by simp⟩, hord.1, ?_, ?_⟩ (Or.inl ?_)
  · intro x
    have h1 : l.toFinset = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [List.toFinset_card_of_nodup hord.1, hord.2, Fintype.card_fin]
    constructor
    · intro _
      simp
    · intro _
      exact List.mem_toFinset.mp (by
        rw [h1]
        exact Finset.mem_univ x)
  · intro x _ y _ _
    have hgg : gameGraph (patternGraph A) ([] : List (Fin n))
        = patternGraph A := rfl
    rw [hgg, hpat]
    exact hadjG x y
  · intro x y hdist
    rw [schurEntry_empty]
    exact patternGraph_adj_entry hA
      (hpat.symm ▸ (hadjG x y).mpr hdist)

end CholeskyCancellations

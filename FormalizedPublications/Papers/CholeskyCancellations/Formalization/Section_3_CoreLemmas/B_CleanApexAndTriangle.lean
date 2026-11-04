/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Logic.Relation
import Mathlib.Analysis.LocallyConvex.Separation
import Section_3_CoreLemmas.A_FarkasAlternative

/-! # Clean apexes and the Triangle Lemma (paper Section 3)

Zeroes at the empty level, the exchange setup, the Triangle Lemma (paper Lemma 3.2) with its three-route case split, and the spoils example.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as the Section 2 files — entries only through `schurEntry`, levels as finsets with enumerating lists wherever the symbolic graph `G_S` is read, cancellations only through `Zeroes`/`logMag`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- At the empty level, `Zeroes` is the paper's displayed equation
(paper Definition 2.19 at `S = ∅`, via `schurEntry_empty`). -/
theorem zeroes_empty_iff {A : Matrix (Fin n) (Fin n) ℝ}
    {u j k : Fin n} (_huj : u ≠ j) (_huk : u ≠ k) (_hjk : j ≠ k) :
    Zeroes A ∅ u j k ↔ A u u * A j k = A u j * A u k := by
  unfold Zeroes
  simp [schurEntry_empty, Ne.symm _huj, Ne.symm _huk, _hjk]



/-- The Exchange Lemma (paper Lemma 3.1, `lem:exchange`): if `u`
cancels `(j, k)` with `A_{uk} ≠ 0`, then `j` does not cancel
`(u, k)`. -/
theorem exchange (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (u j k : Fin n) (huj : u ≠ j) (_huk : u ≠ k) (_hjk : j ≠ k)
    (hak : A u k ≠ 0) (h1 : A u u * A j k = A u j * A u k) :
    A j j * A u k ≠ A j u * A j k := by
  intro h2
  have hdiag_j : (0 : ℝ) < A j j := hA.diag_pos
  have hsymm : ∀ x y : Fin n, A x y = A y x :=
    fun x y => posDef_apply_comm hA x y
  rcases eq_or_ne (A j k) 0 with hjk0 | hjk0
  · rw [hjk0, mul_zero] at h2
    exact mul_ne_zero (ne_of_gt hdiag_j) hak h2
  · have hkey : A u u * A j j * A u k = A u j ^ 2 * A u k := by
      have s : A j u = A u j := hsymm j u
      linear_combination (A u u) * h2 + (A j u) * h1 + (A u j * A u k) * s
    have hcancel : A u u * A j j = A u j ^ 2 := mul_right_cancel₀ hak hkey
    have hminor := posDef_two_mul_sub_pos hA huj
    have hsq : A u j * A j u = A u j ^ 2 := by
      rw [hsymm j u]; ring
    linarith



/-- At the empty level, zeroeing is symmetric in the cancelled pair
(for SPD `A`, by entry symmetry; feeds the Triangle Lemma). -/
theorem zeroes_empty_comm {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {p a b : Fin n}
    (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b)
    (h : Zeroes A ∅ p a b) : Zeroes A ∅ p b a := by
  rw [zeroes_empty_iff hpa hpb hab] at h
  rw [zeroes_empty_iff hpb hpa (Ne.symm hab)]
  rw [posDef_apply_comm hA b a, mul_comm (A p b) (A p a)]
  exact h



/-- A vertex whose one possible route over a triple does not cancel
is a clean apex for that triple (the bookkeeping half of paper
Lemma 3.2: the cancelled pair must be the opposite pair). -/
theorem clean_apex_of_not_zeroes {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {x y z : Fin n} {T : Finset (Fin n)}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hT : ∀ a ∈ T, a = x ∨ a = y ∨ a = z)
    (hnot : ¬ Zeroes A ∅ x y z) : IsCleanApexFor A ∅ x T := by
  intro a ha b hb hz
  have ha0 : a ≠ x := by simpa using hz.2.1
  have hb0 : b ≠ x := by simpa using hz.2.2.1
  have hab : a ≠ b := hz.2.2.2.1
  rcases hT a ha with rfl | rfl | rfl
  · exact absurd rfl ha0
  · rcases hT b hb with rfl | rfl | rfl
    · exact absurd rfl hb0
    · exact absurd rfl hab
    · exact hnot hz
  · rcases hT b hb with rfl | rfl | rfl
    · exact absurd rfl hb0
    · exact hnot (zeroes_empty_comm hA hxz hxy (Ne.symm hyz) hz)
    · exact absurd rfl hab

set_option maxHeartbeats 800000 in


-- The three-route case split below exceeds the default heartbeat budget.
/-- The Triangle Lemma (paper Lemma 3.2, `lem:tri`): at most one apex
route of a triangle cancels, so at least two of its vertices are
clean apexes for it. -/
theorem triangle (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (j k u : Fin n) (hjk : j ≠ k) (hju : j ≠ u) (hku : k ≠ u)
    (_hjk' : A j k ≠ 0) (huk' : A u k ≠ 0) (huj' : A u j ≠ 0) :
    (¬ (Zeroes A ∅ u j k ∧ Zeroes A ∅ j u k)
        ∧ ¬ (Zeroes A ∅ u j k ∧ Zeroes A ∅ k u j)
        ∧ ¬ (Zeroes A ∅ j u k ∧ Zeroes A ∅ k u j))
      ∧ ∃ x ∈ ({j, k, u} : Finset (Fin n)),
          ∃ y ∈ ({j, k, u} : Finset (Fin n)), x ≠ y ∧
            IsCleanApexFor A ∅ x {j, k, u}
              ∧ IsCleanApexFor A ∅ y {j, k, u} := by
  have hsymm : ∀ x y : Fin n, A x y = A y x :=
    fun x y => posDef_apply_comm hA x y
  have eU : Zeroes A ∅ u j k → A u u * A j k = A u j * A u k :=
    (zeroes_empty_iff (Ne.symm hju) (Ne.symm hku) hjk).mp
  have eJ : Zeroes A ∅ j u k → A j j * A u k = A j u * A j k :=
    (zeroes_empty_iff hju hjk (Ne.symm hku)).mp
  have eK : Zeroes A ∅ k u j → A k k * A u j = A k u * A k j :=
    (zeroes_empty_iff hku (Ne.symm hjk) (Ne.symm hju)).mp
  have notJ : Zeroes A ∅ u j k → ¬ Zeroes A ∅ j u k := by
    intro hU hJ
    exact exchange A hA u j k (Ne.symm hju) (Ne.symm hku) hjk
      huk' (eU hU) (eJ hJ)
  have notK1 : Zeroes A ∅ u j k → ¬ Zeroes A ∅ k u j := by
    intro hU hK
    have eU' : A u u * A k j = A u k * A u j := by
      have h := eU hU
      rw [hsymm j k, mul_comm (A u j)] at h
      exact h
    exact exchange A hA u k j (Ne.symm hku) (Ne.symm hju)
      (Ne.symm hjk) huj' eU' (eK hK)
  have notK2 : Zeroes A ∅ j u k → ¬ Zeroes A ∅ k u j := by
    intro hJ hK
    have eJ' : A j j * A k u = A j k * A j u := by
      have h := eJ hJ
      rw [hsymm u k, mul_comm (A j u)] at h
      exact h
    have eK' : A k k * A j u = A k j * A k u := by
      have h := eK hK
      rw [hsymm u j, mul_comm (A k u)] at h
      exact h
    exact exchange A hA j k u hjk hju hku
      (by rw [hsymm j u]; exact huj') eJ' eK'
  refine ⟨⟨fun h => notJ h.1 h.2, fun h => notK1 h.1 h.2,
    fun h => notK2 h.1 h.2⟩, ?_⟩
  have hTj : ∀ a ∈ ({j, k, u} : Finset (Fin n)), a = j ∨ a = u ∨ a = k := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    tauto
  have hTk : ∀ a ∈ ({j, k, u} : Finset (Fin n)), a = k ∨ a = u ∨ a = j := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    tauto
  have hTu : ∀ a ∈ ({j, k, u} : Finset (Fin n)), a = u ∨ a = j ∨ a = k := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    tauto
  by_cases hU : Zeroes A ∅ u j k
  · exact ⟨j, by simp, k, by simp, hjk,
      clean_apex_of_not_zeroes hA hju hjk (Ne.symm hku) hTj (notJ hU),
      clean_apex_of_not_zeroes hA hku (Ne.symm hjk) (Ne.symm hju) hTk
        (notK1 hU)⟩
  · by_cases hJ : Zeroes A ∅ j u k
    · exact ⟨u, by simp, k, by simp, Ne.symm hku,
        clean_apex_of_not_zeroes hA (Ne.symm hju) (Ne.symm hku) hjk hTu hU,
        clean_apex_of_not_zeroes hA hku (Ne.symm hjk) (Ne.symm hju) hTk
          (notK2 hJ)⟩
    · exact ⟨u, by simp, j, by simp, Ne.symm hju,
        clean_apex_of_not_zeroes hA (Ne.symm hju) (Ne.symm hku) hjk hTu hU,
        clean_apex_of_not_zeroes hA hju hjk (Ne.symm hku) hTj hJ⟩



/-- A pair is zeroed by the pivot at `p` exactly when its entry
vanishes after the pivot (paper Definition 2.19 against
`schur_quotient`). -/
theorem zeroes_iff_entry_eq_zero (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) {S : Finset (Fin n)} {p j k : Fin n}
    (hp : p ∉ S) (hj : j ∉ insert p S) (hk : k ∉ insert p S)
    (hjk : j ≠ k) :
    Zeroes A S p j k ↔ schurEntry A (insert p S) j k = 0 := by
  have hd : schurEntry A S p p ≠ 0 := ne_of_gt (schurEntry_pos hA S hp)
  rw [schur_quotient hA S p hp j k hj hk]
  unfold Zeroes pivotEntry
  rw [schurEntry_symm hA S j p, schurEntry_symm hA S k p]
  constructor
  · rintro ⟨-, -, -, -, h⟩
    field_simp
    linarith
  · intro h
    refine ⟨hp, hj, hk, hjk, ?_⟩
    have h2 : schurEntry A S j k
        = schurEntry A S p j * schurEntry A S p k
          / schurEntry A S p p := by linarith
    rw [eq_div_iff hd] at h2
    linarith



/-- The first claim of paper Example 2.31 (`ex:spoils`), for an
arbitrary pair in arbitrary order: the level-`∅` slot on `{j, k}`
spoils every ordering whose first vertex is `j` or `k`, provided
`{j, k}` is an edge of the pattern. -/
theorem slot_empty_spoils_of_head (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : List (Fin n)) {j k : Fin n} (hjk : j ≠ k)
    (hadj : (patternGraph A).Adj j k)
    (hhead : σ.head? = some j ∨ σ.head? = some k) :
    (⟨∅, j, k, by simp, by simp, hjk⟩ : Slot n).Spoils A σ := by
  cases σ with
  | nil => simp at hhead
  | cons x t =>
      simp only [List.head?_cons, Option.some_inj] at hhead
      have hpre : prefixList (x :: t) j k = [] := by
        apply List.takeWhile_cons_of_neg
        intro h
        have h' : x ≠ j ∧ x ≠ k := of_decide_eq_true h
        rcases hhead with rfl | rfl
        · exact h'.1 rfl
        · exact h'.2 rfl
      unfold Slot.Spoils
      refine ⟨?_, ?_⟩
      · change (∅ : Finset (Fin n)) = prefixSet (x :: t) j k
        rw [prefixSet, hpre]
        simp
      · change (gameGraph (patternGraph A)
          (prefixList (x :: t) j k)).Adj j k
        rw [hpre]
        exact hadj



/-- Spoiling and blocking (paper Example 2.31, `ex:spoils`): the
slot `(∅, 0, 1)` spoils every ordering of `Fin 3` whose first
vertex is `0` or `1` (in general `slot_empty_spoils_of_head`); for
the complete pattern on `Fin 3` the three apex slots form a
blocking family, which is not realizable by the Triangle Lemma
(`triangle`). The blocking claim is intrinsically about orderings
of the three triangle vertices, so it is stated at `n = 3`. -/
theorem spoils_example :
    (∀ (A : Matrix (Fin 3) (Fin 3) ℝ) (σ : List (Fin 3)),
      (patternGraph A).Adj 0 1 → IsOrdering σ →
      (σ.head? = some 0 ∨ σ.head? = some 1) →
      (⟨∅, 0, 1, by simp, by simp, by decide⟩ : Slot 3).Spoils
        A σ) ∧
    (∀ (G : SimpleGraph (Fin 3)),
      (∀ x y : Fin 3, x ≠ y → G.Adj x y) →
      IsBlocking {⟨{0}, 1, 2, by decide, by decide, by decide⟩,
        ⟨{1}, 0, 2, by decide, by decide, by decide⟩,
        ⟨{2}, 0, 1, by decide, by decide, by decide⟩} G ∧
      ¬ IsRealizable {⟨{0}, 1, 2, by decide, by decide, by decide⟩,
        ⟨{1}, 0, 2, by decide, by decide, by decide⟩,
        ⟨{2}, 0, 1, by decide, by decide, by decide⟩} G) := by
  classical
  constructor
  · intro A σ hadj01 _ hhead
    exact slot_empty_spoils_of_head A σ (by decide) hadj01 hhead
  · intro G hcomplete
    constructor
    · intro A hpat σ hσ
      obtain ⟨hσnd, hσlen⟩ := hσ
      cases σ with
      | nil => simp at hσlen
      | cons a t =>
          have htlen : t.length = 2 := by
            have h2 : t.length + 1 = 3 := hσlen
            omega
          cases t with
          | nil => simp at htlen
          | cons b t' =>
              have hab : a ≠ b := by
                have h2 := List.nodup_cons.mp hσnd
                intro h
                apply h2.1
                rw [h]
                exact List.mem_cons_self
              have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by
                fin_cases a <;> decide
              have hb3 : b = 0 ∨ b = 1 ∨ b = 2 := by
                fin_cases b <;> decide
              have hadjfull : ∀ x y : Fin 3, x ≠ y →
                  (patternGraph A).Adj x y := by
                intro x y hxy
                rw [hpat]
                exact hcomplete x y hxy
              have spoil_of : ∀ (v j k : Fin 3) (s : Slot 3),
                  s.level = {v} → s.fst = j → s.snd = k →
                  prefixList (a :: b :: t') j k = [v] →
                  s ∈ ({⟨{0}, 1, 2, by decide, by decide,
                      by decide⟩,
                    ⟨{1}, 0, 2, by decide, by decide, by decide⟩,
                    ⟨{2}, 0, 1, by decide, by decide,
                      by decide⟩} : Set (Slot 3)) →
                  s.Spoils A (a :: b :: t') := by
                intro v j k s hl hf hs hpre _
                unfold Slot.Spoils
                refine ⟨?_, ?_⟩
                · rw [hl, hf, hs, prefixSet, hpre]
                  simp
                · have h3 : gameGraph (patternGraph A) [v]
                      = elimStep (patternGraph A) v := rfl
                  rw [hf, hs, hpre, h3]
                  exact elimStep_adj_of_adj _ _ _ _
                    (hadjfull j k (by
                      have := s.hne
                      rwa [hf, hs] at this))
              have pre_of : ∀ (j k : Fin 3), a ≠ j → a ≠ k →
                  (b = j ∨ b = k) →
                  prefixList (a :: b :: t') j k = [a] := by
                intro j k haj hak hb
                change ((a :: b :: t').takeWhile
                  fun x => x ≠ j ∧ x ≠ k) = [a]
                rw [List.takeWhile_cons_of_pos (by
                      simp only [decide_eq_true_eq]
                      exact ⟨haj, hak⟩),
                  List.takeWhile_cons_of_neg (by
                    intro h
                    have h' : b ≠ j ∧ b ≠ k := of_decide_eq_true h
                    rcases hb with rfl | rfl
                    · exact h'.1 rfl
                    · exact h'.2 rfl)]
              rcases ha3 with rfl | rfl | rfl
              · refine ⟨⟨{0}, 1, 2, by decide, by decide,
                  by decide⟩, by simp, ?_⟩
                rcases hb3 with h | h | h
                · exact absurd h.symm hab
                · exact spoil_of 0 1 2 _ rfl rfl rfl
                    (pre_of 1 2 (by decide) (by decide)
                      (Or.inl h)) (by simp)
                · exact spoil_of 0 1 2 _ rfl rfl rfl
                    (pre_of 1 2 (by decide) (by decide)
                      (Or.inr h)) (by simp)
              · refine ⟨⟨{1}, 0, 2, by decide, by decide,
                  by decide⟩, by simp, ?_⟩
                rcases hb3 with h | h | h
                · exact spoil_of 1 0 2 _ rfl rfl rfl
                    (pre_of 0 2 (by decide) (by decide)
                      (Or.inl h)) (by simp)
                · exact absurd h.symm hab
                · exact spoil_of 1 0 2 _ rfl rfl rfl
                    (pre_of 0 2 (by decide) (by decide)
                      (Or.inr h)) (by simp)
              · refine ⟨⟨{2}, 0, 1, by decide, by decide,
                  by decide⟩, by simp, ?_⟩
                rcases hb3 with h | h | h
                · exact spoil_of 2 0 1 _ rfl rfl rfl
                    (pre_of 0 1 (by decide) (by decide)
                      (Or.inl h)) (by simp)
                · exact spoil_of 2 0 1 _ rfl rfl rfl
                    (pre_of 0 1 (by decide) (by decide)
                      (Or.inr h)) (by simp)
                · exact absurd h.symm hab
    · rintro ⟨A, hA, hpat, hact⟩
      have hentry : ∀ {i j : Fin 3}, i ≠ j → A i j ≠ 0 := by
        intro i j hij
        have hadj : (patternGraph A).Adj i j := by
          rw [hpat]
          exact hcomplete i j hij
        have h2 : i ≠ j ∧ (A i j ≠ 0 ∨ A j i ≠ 0) := by
          simpa [patternGraph, SimpleGraph.fromRel_adj] using hadj
        rcases h2.2 with h | h
        · exact h
        · rwa [posDef_apply_comm hA] at h
      have hz1 : Zeroes A ∅ 0 1 2 := by
        rw [zeroes_iff_entry_eq_zero A hA (by simp) (by decide)
          (by decide) (by decide), Finset.insert_eq]
        exact hact ⟨{0}, 1, 2, by decide, by decide, by decide⟩
          (by simp)
      have hz2 : Zeroes A ∅ 1 0 2 := by
        rw [zeroes_iff_entry_eq_zero A hA (by simp) (by decide)
          (by decide) (by decide), Finset.insert_eq]
        exact hact ⟨{1}, 0, 2, by decide, by decide, by decide⟩
          (by simp)
      have htri := (triangle A hA 1 2 0 (by decide) (by decide)
        (by decide) (hentry (by decide)) (hentry (by decide))
        (hentry (by decide))).1.1
      exact htri ⟨hz1, hz2⟩

end CholeskyCancellations

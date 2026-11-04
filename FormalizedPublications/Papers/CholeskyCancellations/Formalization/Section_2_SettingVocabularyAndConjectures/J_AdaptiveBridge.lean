/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Section_2_SettingVocabularyAndConjectures.I_CoveringReformulation

/-! # Adaptive strategies from clean orderings (paper Section 2)

Paper Definition 2.25 (`def:strategy`) calls a pattern `G` adaptively clean when one pivot rule,
reading only the current Schur complement `A/A_S`, produces a clean ordering for every SPD matrix
with pattern `G`. This file proves that this asks for no more than a clean ordering for each such
matrix (`perMatrix_iff_adaptiveStrategy`, for `0 < n`; for `n = 0` there is no pivot rule at all,
`not_patternAdmitsAdaptiveStrategy_zero`).

The reason is that the rest of an ordering, from a level `S` on, is clean or not according to
`S` and `A/A_S` alone: the later Schur complements are pivot updates of `A/A_S` (paper Lemma 2.4,
`schur_quotient`), and a pair is predicted nonzero exactly when the pattern joins it through the
vertices eliminated before it (paper Proposition 2.10, `fill_path`). `CleanContinuationFrom`
states this condition in terms of `S`, the current matrix and `G` only, and
`isCleanOrdering_iff_cleanFrom` checks that from the empty level it is cleanliness. The rule
`cleanNext`, which pivots a vertex beginning a clean continuation, is therefore a function of `S`
and `A/A_S`, and following it never loses the clean continuation it started from
(`runStrategy_cleanNext`): it is an adaptive clean strategy
(`perMatrix_implies_adaptiveStrategy`).
-/

open scoped Matrix

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): vertices `Fin n`, SPD = `Matrix.PosDef`,
levels `Finset (Fin n)`, pivot-order list orderings, Schur entries through `schurEntry` only.
(Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}



/-- `pivotStep M p`: the pivot update at `p` (paper Definition 2.6, `def:pivot`) applied to a
full matrix, `M_{jk} - M_{jp} M_{kp} / M_{pp}`. Only its entries between survivors are ever
read. -/
noncomputable def pivotStep (M : Matrix (Fin n) (Fin n) ℝ) (p : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun j k => M j k - M j p * M k p / M p p



/-- `IsContinuation S l`: `l` lists the survivors `V \ S` of the level `S`, each once (the
continuations of paper Definition 4.7, from an arbitrary level). -/
def IsContinuation (S : Finset (Fin n)) (l : List (Fin n)) : Prop :=
  l.Nodup ∧ ∀ x : Fin n, x ∈ l ↔ x ∉ S



/-- `CleanContinuationFrom G S M l`: from the level `S`, with current Schur complement `M` (read
only between survivors), pivoting in the order `l` commits no zero at a predicted-nonzero
position. Each pivot `p` must be nonzero against every later `k` that `G` joins to `p` through
the current level (paper Definitions 2.24 and 4.7, with Proposition 2.10's path form of the fill
graph). The condition mentions `S`, `M` and `G` only, never the matrix that produced `M`. -/
def CleanContinuationFrom (G : SimpleGraph (Fin n)) :
    Finset (Fin n) → Matrix (Fin n) (Fin n) ℝ → List (Fin n) → Prop
  | _, _, [] => True
  | S, M, p :: l => (∀ k ∈ l, HasPathThrough G S p k → M p k ≠ 0) ∧
      CleanContinuationFrom G (insert p S) (pivotStep M p) l



open Classical in
/-- `cleanNext G d S M`: the pivot rule of the bridge. At the level `S` with current Schur
complement `M` it pivots a vertex that begins a clean continuation, if there is one (and the
default `d` otherwise). It is a function of `S` and `M` alone, as paper Definition 2.25 requires
of an adaptive strategy. -/
noncomputable def cleanNext (G : SimpleGraph (Fin n)) (d : Fin n) (S : Finset (Fin n))
    (M : Matrix (Fin n) (Fin n) ℝ) : Fin n :=
  if h : ∃ p : Fin n, ∃ l : List (Fin n),
      IsContinuation S (p :: l) ∧ CleanContinuationFrom G S M (p :: l)
  then h.choose else d



/-- `runStrategy next A r S`: the `r` pivots that the rule `next` makes for `A`, starting at the
level `S` (paper Definition 2.25: an adaptive strategy produces an ordering `σ(A)`). -/
noncomputable def runStrategy (next : Finset (Fin n) → Matrix (Fin n) (Fin n) ℝ → Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → Finset (Fin n) → List (Fin n)
  | 0, _ => []
  | r + 1, S => next S (schurMatrix A S) ::
      runStrategy next A r (insert (next S (schurMatrix A S)) S)



/-- The pivot update preserves agreement with the Schur complement (paper Lemma 2.4,
`schur_quotient`): if `M` agrees with `A/A_S` between survivors, then `pivotStep M p` agrees with
`A/A_{S ∪ {p}}` between the new survivors. -/
theorem pivotStep_agree (hA : A.PosDef) {S : Finset (Fin n)} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ j k : Fin n, j ∉ S → k ∉ S → M j k = schurEntry A S j k) {p : Fin n}
    (hp : p ∉ S) (j k : Fin n) (hj : j ∉ insert p S) (hk : k ∉ insert p S) :
    pivotStep M p j k = schurEntry A (insert p S) j k := by
  have hjS : j ∉ S := fun h => hj (Finset.mem_insert_of_mem h)
  have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
  rw [schur_quotient hA S p hp j k hj hk, pivotEntry]
  simp only [pivotStep, Matrix.of_apply, hM j k hjS hkS, hM j p hjS hp, hM k p hkS hp,
    hM p p hp hp]



/-- A continuation avoiding `S` and starting with `p` avoids `insert p S` after `p`. -/
theorem notMem_insert_of_cons {p : Fin n} {l : List (Fin n)} {S : Finset (Fin n)}
    (hnd : (p :: l).Nodup) (hdisj : ∀ x ∈ p :: l, x ∉ S) : ∀ x ∈ l, x ∉ insert p S := by
  intro x hx hxS
  rcases Finset.mem_insert.mp hxS with rfl | hxS
  · exact (List.nodup_cons.mp hnd).1 hx
  · exact hdisj x (List.mem_cons_of_mem p hx) hxS



/-- `CleanContinuationFrom` reads the current matrix only between survivors. -/
theorem cleanFrom_congr (G : SimpleGraph (Fin n)) :
    ∀ (l : List (Fin n)) (S : Finset (Fin n)) (M M' : Matrix (Fin n) (Fin n) ℝ),
      l.Nodup → (∀ x ∈ l, x ∉ S) → (∀ j k : Fin n, j ∉ S → k ∉ S → M j k = M' j k) →
        (CleanContinuationFrom G S M l ↔ CleanContinuationFrom G S M' l)
  | [], _, _, _, _, _, _ => Iff.rfl
  | p :: l, S, M, M', hnd, hdisj, hMM' => by
    have hpS : p ∉ S := hdisj p List.mem_cons_self
    have hagree : ∀ j k : Fin n, j ∉ insert p S → k ∉ insert p S →
        pivotStep M p j k = pivotStep M' p j k := by
      intro j k hj hk
      have hjS : j ∉ S := fun h => hj (Finset.mem_insert_of_mem h)
      have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
      simp only [pivotStep, Matrix.of_apply, hMM' j k hjS hkS, hMM' j p hjS hpS,
        hMM' k p hkS hpS, hMM' p p hpS hpS]
    have hhead : ∀ k ∈ l, M p k = M' p k := fun k hk =>
      hMM' p k hpS (hdisj k (List.mem_cons_of_mem p hk))
    simp only [CleanContinuationFrom]
    rw [cleanFrom_congr G l (insert p S) (pivotStep M p) (pivotStep M' p)
      (List.nodup_cons.mp hnd).2 (notMem_insert_of_cons hnd hdisj) hagree]
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨fun k hk hpath => ?_, h₂⟩
      rw [← hhead k hk]
      exact h₁ k hk hpath
    · rintro ⟨h₁, h₂⟩
      refine ⟨fun k hk hpath => ?_, h₂⟩
      rw [hhead k hk]
      exact h₁ k hk hpath



/-- `CleanContinuationFrom` unrolled: from a level `S` at which `M` agrees with `A/A_S`, the
continuation `l` is clean iff every pivot `p` of `l` is nonzero, at its own level, against every
later `k` that the pattern joins to `p` through that level. -/
theorem cleanFrom_iff (hA : A.PosDef) :
    ∀ (l : List (Fin n)) (S : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℝ),
      l.Nodup → (∀ x ∈ l, x ∉ S) →
        (∀ j k : Fin n, j ∉ S → k ∉ S → M j k = schurEntry A S j k) →
        (CleanContinuationFrom (patternGraph A) S M l ↔
          ∀ (l₁ : List (Fin n)) (p : Fin n) (l₂ : List (Fin n)), l = l₁ ++ p :: l₂ →
            ∀ k ∈ l₂, HasPathThrough (patternGraph A) (S ∪ l₁.toFinset) p k →
              schurEntry A (S ∪ l₁.toFinset) p k ≠ 0)
  | [], _, _, _, _, _ => by
    simp only [CleanContinuationFrom, true_iff]
    intro l₁ p l₂ h
    simp at h
  | p₀ :: l, S, M, hnd, hdisj, hM => by
    have hp₀S : p₀ ∉ S := hdisj p₀ List.mem_cons_self
    have hset : ∀ l₁ : List (Fin n), S ∪ (p₀ :: l₁).toFinset = insert p₀ S ∪ l₁.toFinset := by
      intro l₁
      ext x
      simp only [Finset.mem_union, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset]
      tauto
    simp only [CleanContinuationFrom]
    rw [cleanFrom_iff hA l (insert p₀ S) (pivotStep M p₀) (List.nodup_cons.mp hnd).2
      (notMem_insert_of_cons hnd hdisj) (pivotStep_agree hA hM hp₀S)]
    constructor
    · rintro ⟨h₁, h₂⟩ l₁ p l₂ hsplit k hk hpath
      cases l₁ with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hsplit
        obtain ⟨hp, hl⟩ := hsplit
        subst hp hl
        simp only [List.toFinset_nil, Finset.union_empty] at hpath ⊢
        rw [← hM p₀ k hp₀S (hdisj k (List.mem_cons_of_mem p₀ hk))]
        exact h₁ k hk hpath
      | cons q l₁ =>
        simp only [List.cons_append, List.cons.injEq] at hsplit
        obtain ⟨hq, hsplit⟩ := hsplit
        subst hq
        rw [hset] at hpath ⊢
        exact h₂ l₁ p l₂ hsplit k hk hpath
    · intro h
      refine ⟨fun k hk hpath => ?_, fun l₁ p l₂ hsplit k hk hpath => ?_⟩
      · have h' := h [] p₀ l rfl k hk (by simpa using hpath)
        rw [hM p₀ k hp₀S (hdisj k (List.mem_cons_of_mem p₀ hk))]
        simpa using h'
      · have h' := h (p₀ :: l₁) p l₂ (by rw [hsplit]; rfl) k hk (by rw [hset]; exact hpath)
        rwa [hset] at h'



/-- The committing prefix of `p` and a later `k` in `l₁ ++ p :: l₂` is `l₁` (paper
Definition 2.24's level, read off the split). -/
theorem prefixList_of_split {σ l₁ l₂ : List (Fin n)} {p k : Fin n}
    (hσ : σ = l₁ ++ p :: l₂) (hp : p ∉ l₁) (hk : k ∉ l₁) : prefixList σ p k = l₁ := by
  subst hσ
  unfold prefixList
  rw [takeWhile_append_of_forall (fun x hx => by
    have h1 : x ≠ p := fun h => hp (h ▸ hx)
    have h2 : x ≠ k := fun h => hk (h ▸ hx)
    simp [h1, h2])]
  simp



/-- Cleanliness of an ordering (paper Definition 2.24) is a clean continuation from the empty
level, whose current matrix is `A` itself. -/
theorem isCleanOrdering_iff_cleanFrom (hA : A.PosDef) {σ : List (Fin n)} (hσ : IsOrdering σ) :
    IsCleanOrdering A σ ↔ CleanContinuationFrom (patternGraph A) ∅ (schurMatrix A ∅) σ := by
  rw [cleanFrom_iff hA σ ∅ (schurMatrix A ∅) hσ.1 (fun x _ => Finset.notMem_empty x)
    (fun _ _ _ _ => rfl)]
  simp only [Finset.empty_union]
  -- In a split `σ = l₁ ++ p :: l₂`, the part `l₁` avoids `p` and everything after it.
  have hsplit_facts : ∀ (l₁ : List (Fin n)) (p : Fin n) (l₂ : List (Fin n)),
      σ = l₁ ++ p :: l₂ → p ∉ l₁ ∧ (∀ k ∈ l₂, k ∉ l₁) ∧ p ∉ l₂ := by
    intro l₁ p l₂ hsplit
    have hnd := hσ.1
    rw [hsplit] at hnd
    have hdisj := List.disjoint_of_nodup_append hnd
    exact ⟨fun h => hdisj h List.mem_cons_self,
      fun k hk h => hdisj h (List.mem_cons_of_mem p hk),
      (List.nodup_cons.mp (List.Nodup.of_append_right hnd)).1⟩
  constructor
  · intro hclean l₁ p l₂ hsplit k hk hpath
    obtain ⟨hp₁, hk₁, hp₂⟩ := hsplit_facts l₁ p l₂ hsplit
    have hpk : p ≠ k := fun h => hp₂ (h ▸ hk)
    have hpre : prefixSet σ p k = l₁.toFinset := by
      rw [prefixSet, prefixList_of_split hsplit hp₁ (hk₁ k hk)]
    have hpred : PredictedNonzero A σ p k := by
      rw [PredictedNonzero, (fill_path σ hσ p k hpk).1, (fill_path σ hσ p k hpk).2, hpre]
      exact hpath
    have h' := hclean p k hpred
    rwa [hpre] at h'
  · intro h j k hpred
    have hadj : (fillGraph A σ).Adj j k := hpred
    have hjk : j ≠ k := hadj.ne
    obtain ⟨s, t, hst⟩ := List.append_of_mem (fill_mem_of_isOrdering hσ j)
    have hkσ := fill_mem_of_isOrdering hσ k
    rw [hst] at hkσ
    rcases List.mem_append.mp hkσ with hks | hkt
    · -- `k` comes first
      obtain ⟨s₁, s₂, hs⟩ := List.append_of_mem hks
      have hsplit : σ = s₁ ++ k :: (s₂ ++ j :: t) := by rw [hst, hs]; simp
      obtain ⟨hk₁, hj₁, -⟩ := hsplit_facts s₁ k (s₂ ++ j :: t) hsplit
      have hj' : j ∈ s₂ ++ j :: t := by simp
      have hpre : prefixSet σ k j = s₁.toFinset := by
        rw [prefixSet, prefixList_of_split hsplit hk₁ (hj₁ j hj')]
      have hpath : HasPathThrough (patternGraph A) s₁.toFinset k j := by
        have hadj' : (fillGraph A σ).Adj k j := hadj.symm
        rw [(fill_path σ hσ k j hjk.symm).1, (fill_path σ hσ k j hjk.symm).2, hpre] at hadj'
        exact hadj'
      have h' := h s₁ k (s₂ ++ j :: t) hsplit j hj' hpath
      rw [← prefixSet_comm σ j k, hpre, schurEntry_symm hA]
      exact h'
    · -- `j` comes first
      have hkt : k ∈ t := by
        rcases List.mem_cons.mp hkt with h' | h'
        · exact absurd h'.symm hjk
        · exact h'
      obtain ⟨hj₁, hk₁, -⟩ := hsplit_facts s j t hst
      have hpre : prefixSet σ j k = s.toFinset := by
        rw [prefixSet, prefixList_of_split hst hj₁ (hk₁ k hkt)]
      have hpath : HasPathThrough (patternGraph A) s.toFinset j k := by
        have hadj' := hadj
        rw [(fill_path σ hσ j k hjk).1, (fill_path σ hσ j k hjk).2, hpre] at hadj'
        exact hadj'
      rw [hpre]
      exact h s j t hst k hkt hpath



/-- The rule `cleanNext` keeps its promise: when some vertex begins a clean continuation, the
vertex it pivots does. -/
theorem cleanNext_spec (G : SimpleGraph (Fin n)) (d : Fin n) {S : Finset (Fin n)}
    {M : Matrix (Fin n) (Fin n) ℝ}
    (h : ∃ p : Fin n, ∃ l : List (Fin n),
      IsContinuation S (p :: l) ∧ CleanContinuationFrom G S M (p :: l)) :
    ∃ l : List (Fin n), IsContinuation S (cleanNext G d S M :: l) ∧
      CleanContinuationFrom G S M (cleanNext G d S M :: l) := by
  rw [cleanNext, dite_eq_left h]
  exact h.choose_spec



/-- A strategy run of `r` steps makes `r` pivots. -/
theorem runStrategy_length (next : Finset (Fin n) → Matrix (Fin n) (Fin n) ℝ → Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ (r : ℕ) (S : Finset (Fin n)), (runStrategy next A r S).length = r
  | 0, _ => rfl
  | r + 1, S => by simp [runStrategy, runStrategy_length next A r]



/-- Every pivot of `runStrategy next A r S` is the choice `next` makes at the level of the
pivots before it (paper Definition 2.25). -/
theorem runStrategy_follows (next : Finset (Fin n) → Matrix (Fin n) (Fin n) ℝ → Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ (r : ℕ) (S : Finset (Fin n)) (l₁ : List (Fin n)) (p : Fin n) (l₂ : List (Fin n)),
      runStrategy next A r S = l₁ ++ p :: l₂ →
        p = next (S ∪ l₁.toFinset) (schurMatrix A (S ∪ l₁.toFinset))
  | 0, _, l₁, p, l₂, h => by simp [runStrategy] at h
  | r + 1, S, [], p, l₂, h => by
    simp only [runStrategy, List.nil_append, List.cons.injEq] at h
    rw [← h.1]
    simp
  | r + 1, S, q :: l₁, p, l₂, h => by
    simp only [runStrategy, List.cons_append, List.cons.injEq] at h
    obtain ⟨hq, h⟩ := h
    have h' := runStrategy_follows next A r _ l₁ p l₂ h
    have hset : insert (next S (schurMatrix A S)) S ∪ l₁.toFinset
        = S ∪ (q :: l₁).toFinset := by
      rw [hq]
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons, List.mem_toFinset]
      tauto
    rwa [hset] at h'



/-- The run invariant of the bridge: if a clean continuation exists from the level `S`, then
the pivots `cleanNext` makes from `S` on are one. -/
theorem runStrategy_cleanNext (hA : A.PosDef) (d : Fin n) :
    ∀ (r : ℕ) (S : Finset (Fin n)) (l : List (Fin n)), l.length = r → IsContinuation S l →
      CleanContinuationFrom (patternGraph A) S (schurMatrix A S) l →
        IsContinuation S (runStrategy (cleanNext (patternGraph A) d) A r S) ∧
          CleanContinuationFrom (patternGraph A) S (schurMatrix A S)
            (runStrategy (cleanNext (patternGraph A) d) A r S)
  | 0, S, l, hlen, hcont, _ => by
    have hl : l = [] := List.eq_nil_of_length_eq_zero hlen
    subst hl
    exact ⟨hcont, trivial⟩
  | r + 1, S, l, hlen, hcont, hclean => by
    obtain ⟨p', l', rfl⟩ : ∃ p' l', l = p' :: l' := by
      cases l with
      | nil => simp at hlen
      | cons p' l' => exact ⟨p', l', rfl⟩
    obtain ⟨q, hq⟩ : ∃ q, q = cleanNext (patternGraph A) d S (schurMatrix A S) := ⟨_, rfl⟩
    obtain ⟨l₀, hcont₀, hclean₀⟩ := cleanNext_spec (patternGraph A) d ⟨p', l', hcont, hclean⟩
    rw [← hq] at hcont₀ hclean₀
    obtain ⟨hnd₀, hmem₀⟩ := hcont₀
    have hqS : q ∉ S := (hmem₀ q).1 List.mem_cons_self
    have hmem₀' : ∀ x, x ∈ l₀ ↔ x ∉ insert q S := by
      intro x
      constructor
      · exact notMem_insert_of_cons hnd₀ (fun y hy => (hmem₀ y).1 hy) x
      · intro hx
        have hxq : x ≠ q := fun h => hx (h ▸ Finset.mem_insert_self q S)
        have hxS : x ∉ S := fun h => hx (Finset.mem_insert_of_mem h)
        rcases List.mem_cons.mp ((hmem₀ x).2 hxS) with h | h
        · exact absurd h hxq
        · exact h
    have hlen₀ : l₀.length = r := by
      have h1 : (p' :: l').toFinset = (q :: l₀).toFinset := by
        ext x
        simp only [List.mem_toFinset]
        rw [hcont.2 x, hmem₀ x]
      have h2 := congrArg Finset.card h1
      rw [List.toFinset_card_of_nodup hcont.1, List.toFinset_card_of_nodup hnd₀] at h2
      simp only [List.length_cons] at h2 hlen
      omega
    simp only [CleanContinuationFrom] at hclean₀
    obtain ⟨hhead, htail⟩ := hclean₀
    have hdisj₀ : ∀ x ∈ l₀, x ∉ insert q S := fun x hx => (hmem₀' x).1 hx
    have hagree : ∀ j k : Fin n, j ∉ insert q S → k ∉ insert q S →
        pivotStep (schurMatrix A S) q j k = schurMatrix A (insert q S) j k :=
      fun j k hj hk => pivotStep_agree hA (fun _ _ _ _ => rfl) hqS j k hj hk
    have htail' := (cleanFrom_congr (patternGraph A) l₀ (insert q S) _ _
      (List.nodup_cons.mp hnd₀).2 hdisj₀ hagree).1 htail
    obtain ⟨hcontR, hcleanR⟩ := runStrategy_cleanNext hA d r (insert q S) l₀ hlen₀
      ⟨(List.nodup_cons.mp hnd₀).2, hmem₀'⟩ htail'
    have hrun : runStrategy (cleanNext (patternGraph A) d) A (r + 1) S
        = q :: runStrategy (cleanNext (patternGraph A) d) A r (insert q S) := by
      rw [hq]
      rfl
    rw [hrun]
    have hdisjR : ∀ x ∈ runStrategy (cleanNext (patternGraph A) d) A r (insert q S),
        x ∉ insert q S := fun x hx => (hcontR.2 x).1 hx
    refine ⟨⟨List.nodup_cons.mpr ⟨fun h => hdisjR q h (Finset.mem_insert_self q S),
      hcontR.1⟩, fun x => ?_⟩, ?_⟩
    · constructor
      · intro hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hqS
        · exact fun h => hdisjR x hx (Finset.mem_insert_of_mem h)
      · intro hxS
        by_cases hxq : x = q
        · rw [hxq]
          exact List.mem_cons_self
        · refine List.mem_cons_of_mem q ((hcontR.2 x).2 ?_)
          intro h
          rcases Finset.mem_insert.mp h with h | h
          · exact hxq h
          · exact hxS h
    · simp only [CleanContinuationFrom]
      refine ⟨fun k hk hpath => hhead k ((hmem₀' k).2 (hdisjR k hk)) hpath, ?_⟩
      exact (cleanFrom_congr (patternGraph A) _ (insert q S) _ _ hcontR.1 hdisjR hagree).2
        hcleanR



/-- **Per-matrix implies adaptive** (paper Definition 2.25, `def:strategy`): if every SPD
realization of `G` has a clean ordering, then the rule `cleanNext`, which reads only the level
and the current Schur complement, is an adaptive clean strategy for `G`. -/
theorem perMatrix_implies_adaptiveStrategy (hn : 0 < n) {G : SimpleGraph (Fin n)}
    (h : PatternAdmitsPerMatrixCleanOrdering G) : PatternAdmitsAdaptiveStrategy G := by
  refine ⟨cleanNext G ⟨0, hn⟩, ?_⟩
  intro A hA hG
  subst hG
  obtain ⟨σ₀, hσ₀, hclean₀⟩ := h A hA rfl
  have hcont₀ : IsContinuation ∅ σ₀ :=
    ⟨hσ₀.1, fun x => by simp [fill_mem_of_isOrdering hσ₀ x]⟩
  obtain ⟨hcont, hclean⟩ := runStrategy_cleanNext hA ⟨0, hn⟩ n ∅ σ₀ hσ₀.2 hcont₀
    ((isCleanOrdering_iff_cleanFrom hA hσ₀).1 hclean₀)
  have hσ : IsOrdering (runStrategy (cleanNext (patternGraph A) ⟨0, hn⟩) A n ∅) :=
    ⟨hcont.1, runStrategy_length _ A n ∅⟩
  refine ⟨_, hσ, (isCleanOrdering_iff_cleanFrom hA hσ).2 hclean, ?_⟩
  intro l₁ p l₂ hsplit
  simpa using runStrategy_follows _ A n ∅ l₁ p l₂ hsplit



/-- Per-matrix and adaptive clean orderings coincide when `0 < n` (paper Definition 2.25): a
pattern admits an adaptive clean ordering exactly when every SPD realization has a clean
ordering. -/
theorem perMatrix_iff_adaptiveStrategy (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    PatternAdmitsPerMatrixCleanOrdering G ↔ PatternAdmitsAdaptiveStrategy G :=
  ⟨perMatrix_implies_adaptiveStrategy hn, adaptiveStrategy_implies_perMatrix⟩



/-- On the empty vertex set there is no pivot rule at all (`Fin 0` is empty), so the hypothesis
`0 < n` above cannot be dropped, although the empty ordering is clean. -/
theorem not_patternAdmitsAdaptiveStrategy_zero (G : SimpleGraph (Fin 0)) :
    ¬ PatternAdmitsAdaptiveStrategy G := by
  rintro ⟨next, -⟩
  exact (next ∅ 0).elim0

end CholeskyCancellations

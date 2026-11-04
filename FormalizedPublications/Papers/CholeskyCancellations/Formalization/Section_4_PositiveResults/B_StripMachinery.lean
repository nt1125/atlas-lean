/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.TakeWhile
import Section_4_PositiveResults.A_Theorem41Determinants

/-! # Strip machinery (paper Section 4)

Strip patterns and states (paper Definitions 4.3–4.5), end/second pivots, clean continuations, and the one-clean-pivot-prepends step.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as the Section 2 files; graph classes are predicates on `SimpleGraph (Fin n)` patterns and cleanliness is quantified per SPD realization through `PatternAdmitsPerMatrixCleanOrdering`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}



/-- `DistOneIn l x y`: `x` and `y` are consecutive in the list `l`,
in either order (boundary pairs of paper Definition 4.3). -/
def DistOneIn (l : List (Fin n)) (x y : Fin n) : Prop :=
  (∃ l₁ l₂ : List (Fin n), l = l₁ ++ x :: y :: l₂)
    ∨ (∃ l₁ l₂ : List (Fin n), l = l₁ ++ y :: x :: l₂)



/-- `DistTwoIn l x y`: `x` and `y` are at distance two in the list
`l`, in either order (diagonal pairs of paper Definition 4.3). -/
def DistTwoIn (l : List (Fin n)) (x y : Fin n) : Prop :=
  (∃ (l₁ l₂ : List (Fin n)) (z : Fin n), l = l₁ ++ x :: z :: y :: l₂)
    ∨ (∃ (l₁ l₂ : List (Fin n)) (z : Fin n), l = l₁ ++ y :: z :: x :: l₂)



/-- `IsStripPattern G`: `G` is a 2-path strip — its vertices list as
`v₁, …, vₖ` with edges exactly the boundary (distance one) and
diagonal (distance two) pairs (paper Definition 4.3, `def:strip`). -/
def IsStripPattern (G : SimpleGraph (Fin n)) : Prop :=
  3 ≤ n ∧ ∃ l : List (Fin n), IsOrdering l ∧
    ∀ x y : Fin n, G.Adj x y ↔ DistOneIn l x y ∨ DistTwoIn l x y



/-- `IsStripState A lS S l`: `(S, P)` is a strip state — the symbolic
graph at level `S` (enumerated by `lS`) induces a 2-path strip `P` on
the survivors, listed by `l` (paper Definition 4.4,
`def:strip-state`); `l` may use fill edges of `G_S`. -/
def IsStripState (A : Matrix (Fin n) (Fin n) ℝ) (lS : List (Fin n))
    (S : Finset (Fin n)) (l : List (Fin n)) : Prop :=
  Enumerates lS S ∧ l.Nodup ∧ (∀ x : Fin n, x ∈ l ↔ x ∉ S) ∧
    ∀ x ∈ l, ∀ y ∈ l, x ≠ y →
      ((gameGraph (patternGraph A) lS).Adj x y
        ↔ DistOneIn l x y ∨ DistTwoIn l x y)



/-- `StripStateZero A S l`: the strip state is in State 0, every strip
edge nonzero in `A/A_S` (paper Definition 4.4, `def:strip-state`). -/
def StripStateZero (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (l : List (Fin n)) : Prop :=
  ∀ x y : Fin n, DistOneIn l x y ∨ DistTwoIn l x y →
    schurEntry A S x y ≠ 0



/-- `StripStateOne A S l`: the strip state is in State 1, exactly the
pair `(s₂, s₃)` at the left end is zero in `A/A_S` (paper
Definition 4.4, `def:strip-state`). -/
def StripStateOne (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (l : List (Fin n)) : Prop :=
  ∃ s₁ s₂ s₃ : Fin n, ∃ rest : List (Fin n), l = s₁ :: s₂ :: s₃ :: rest ∧
    schurEntry A S s₂ s₃ = 0 ∧
      ∀ x y : Fin n, DistOneIn l x y ∨ DistTwoIn l x y →
        ¬ SamePair x y s₂ s₃ → schurEntry A S x y ≠ 0



/-- `IsEndPivot l p`: pivoting `p` is the END move — `p` is the end
vertex `s₁` of the strip list (paper Definition 4.5,
`def:strip-moves`). The strip moves require `k ≥ 4` survivors, so
a fourth vertex `s₄` is required: a 3-vertex list is not an END
move. (Unused: the strip induction reads the moves off the state
directly.) -/
def IsEndPivot (l : List (Fin n)) (p : Fin n) : Prop :=
  ∃ (s₂ s₃ s₄ : Fin n) (rest : List (Fin n)),
    l = p :: s₂ :: s₃ :: s₄ :: rest



/-- An END move needs at least four survivors (paper
Definition 4.5's `k ≥ 4`). -/
example {l : List (Fin n)} {p : Fin n} (h : IsEndPivot l p) :
    4 ≤ l.length := by
  obtain ⟨_, _, _, rest, rfl⟩ := h
  simp



/-- `IsSecondPivot l p`: pivoting `p` is the SECOND move — `p` is the
second vertex `s₂` of the strip list (paper Definition 4.5,
`def:strip-moves`). -/
def IsSecondPivot (l : List (Fin n)) (p : Fin n) : Prop :=
  ∃ (s₁ s₃ s₄ : Fin n) (rest : List (Fin n)),
    l = s₁ :: p :: s₃ :: s₄ :: rest



/-- `AdmitsCleanContinuation A lS S`: the state at level `S` has a
clean continuation — an ordering `τ` of the survivors each of whose
pivots commits only nonzero predicted entries (paper Definition 4.7,
`def:clean_continuation`). The `Enumerates lS S` conjunct is
load-bearing: `gameGraph (patternGraph A) (lS ++ prefix)` is the
paper's `G_{S_{i-1}}` only when `lS` enumerates `S`, so that
`lS ++ prefix` enumerates the enlarged level. -/
def AdmitsCleanContinuation (A : Matrix (Fin n) (Fin n) ℝ)
    (lS : List (Fin n)) (S : Finset (Fin n)) : Prop :=
  Enumerates lS S ∧
  ∃ τ : List (Fin n), τ.Nodup ∧ (∀ x : Fin n, x ∈ τ ↔ x ∉ S) ∧
    ∀ p x : Fin n, AfterIn τ p x →
      (gameGraph (patternGraph A) (lS ++ prefixListBefore τ p)).Adj p x →
        schurEntry A (S ∪ (prefixListBefore τ p).toFinset) p x ≠ 0



/-- A clean continuation comes with an enumeration of its level. -/
example (A : Matrix (Fin n) (Fin n) ℝ) (lS : List (Fin n))
    (S : Finset (Fin n)) (h : AdmitsCleanContinuation A lS S) :
    Enumerates lS S :=
  h.1



/-- A member splits a list around its occurrence. -/
theorem mem_split_cons {x : Fin n} :
    ∀ {l : List (Fin n)}, x ∈ l → ∃ s t : List (Fin n), l = s ++ x :: t := by
  intro l
  induction l with
  | nil =>
      intro h
      simp at h
  | cons y l ih =>
      intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨[], l, rfl⟩
      · obtain ⟨s, t, ht⟩ := ih h
        exact ⟨y :: s, t, by simp [ht]⟩



/-- In a duplicate-free list, one of two distinct members comes first. -/
theorem afterIn_or : ∀ (τ : List (Fin n)), τ.Nodup → ∀ j k : Fin n,
    j ∈ τ → k ∈ τ → j ≠ k → AfterIn τ j k ∨ AfterIn τ k j := by
  intro τ
  induction τ with
  | nil =>
      intro _ j k hj
      simp at hj
  | cons x τ ih =>
      intro hnd j k hj hk hjk
      rcases List.mem_cons.mp hj with rfl | hjτ
      · rcases List.mem_cons.mp hk with hkk | hkτ
        · exact absurd hkk.symm hjk
        · obtain ⟨s, t, ht⟩ := mem_split_cons hkτ
          exact Or.inl ⟨[], s, t, by simp [ht]⟩
      · rcases List.mem_cons.mp hk with rfl | hkτ
        · obtain ⟨s, t, ht⟩ := mem_split_cons hjτ
          exact Or.inr ⟨[], s, t, by simp [ht]⟩
        · have hnd' := (List.nodup_cons.mp hnd).2
          rcases ih hnd' j k hjτ hkτ hjk with ⟨l₁, l₂, l₃, hl⟩ | ⟨l₁, l₂, l₃, hl⟩
          · exact Or.inl ⟨x :: l₁, l₂, l₃, by simp [hl]⟩
          · exact Or.inr ⟨x :: l₁, l₂, l₃, by simp [hl]⟩



/-- `takeWhile` stops exactly at the first failing element. -/
theorem takeWhile_append_cons_eq (q : Fin n → Bool) :
    ∀ (l₁ : List (Fin n)) (p : Fin n) (rest : List (Fin n)),
      (∀ y ∈ l₁, q y = true) → q p = false →
        (l₁ ++ p :: rest).takeWhile q = l₁ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro p rest _ hp
      simp [hp]
  | cons y l₁ ih =>
      intro p rest hq hp
      have hy : q y = true := hq y (by simp)
      simp only [List.cons_append, List.takeWhile_cons, hy, ite_true]
      rw [ih p rest (fun z hz => hq z (List.mem_cons_of_mem _ hz)) hp]



/-- The committing prefix list of a pair is the prefix before its
earlier member. -/
theorem prefixList_eq_prefixListBefore_of_afterIn {τ : List (Fin n)}
    {p x : Fin n} (hnd : τ.Nodup) (h : AfterIn τ p x) :
    prefixList τ p x = prefixListBefore τ p := by
  obtain ⟨l₁, l₂, l₃, hτ⟩ := h
  have hne : ∀ y ∈ l₁, y ≠ p ∧ y ≠ x := by
    intro y hy
    have hnd' : ((l₁ ++ p :: l₂) ++ x :: l₃).Nodup := hτ ▸ hnd
    obtain ⟨hndA, -, hdisj2⟩ := List.nodup_append.mp hnd'
    obtain ⟨-, -, hdisj1⟩ := List.nodup_append.mp hndA
    exact ⟨hdisj1 y hy p (by simp),
      hdisj2 y (List.mem_append_left _ hy) x (by simp)⟩
  have e1 : prefixList τ p x = l₁ := by
    rw [prefixList, hτ, List.append_assoc, List.cons_append]
    apply takeWhile_append_cons_eq
    · intro y hy
      simp only [decide_eq_true_eq]
      exact hne y hy
    · simp
  have e2 : prefixListBefore τ p = l₁ := by
    rw [prefixListBefore, hτ, List.append_assoc, List.cons_append]
    apply takeWhile_append_cons_eq
    · intro y hy
      simp only [decide_eq_true_eq]
      exact (hne y hy).1
    · simp
  rw [e1, e2]



/-- A clean continuation from the empty level is a clean ordering. -/
theorem exists_clean_of_continuation_empty {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef)
    (h : AdmitsCleanContinuation A [] ∅) :
    ∃ σ : List (Fin n), IsOrdering σ ∧ IsCleanOrdering A σ := by
  classical
  obtain ⟨-, τ, hτnd, hτmem, hτ⟩ := h
  have hmem : ∀ x : Fin n, x ∈ τ := fun x => (hτmem x).mpr (by simp)
  have hlen : τ.length = n := by
    have h1 : τ.toFinset = Finset.univ := by
      ext x
      simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
      exact hmem x
    have h2 := congrArg Finset.card h1
    rw [List.toFinset_card_of_nodup hτnd, Finset.card_univ,
      Fintype.card_fin] at h2
    exact h2
  refine ⟨τ, ⟨hτnd, hlen⟩, ?_⟩
  intro j k hPred
  have hAdj : (fillGraph A τ).Adj j k := hPred
  have hjk : j ≠ k := hAdj.ne
  have hgame : (gameGraph (patternGraph A) (prefixList τ j k)).Adj j k :=
    ((fill_path τ ⟨hτnd, hlen⟩ j k hjk).1).mp hAdj
  rcases afterIn_or τ hτnd j k (hmem j) (hmem k) hjk with hAfter | hAfter
  · have hpre := prefixList_eq_prefixListBefore_of_afterIn hτnd hAfter
    have hgame' : (gameGraph (patternGraph A)
        ([] ++ prefixListBefore τ j)).Adj j k := by
      simpa [hpre] using hgame
    have hcont := hτ j k hAfter hgame'
    simpa [prefixSet, hpre] using hcont
  · have hpre := prefixList_eq_prefixListBefore_of_afterIn hτnd hAfter
    have hlistcomm : prefixList τ j k = prefixList τ k j := by
      rw [prefixList, prefixList]
      exact takeWhile_ext τ _ _ (fun x => by simp [and_comm])
    have hgame' : (gameGraph (patternGraph A)
        ([] ++ prefixListBefore τ k)).Adj k j := by
      have := hgame.symm
      simpa [hlistcomm, hpre] using this
    have hcont := hτ k j hAfter hgame'
    have hset : prefixSet τ j k = ∅ ∪ (prefixListBefore τ k).toFinset := by
      rw [prefixSet_comm, prefixSet, hpre]
      simp
    rw [hset]
    exact fun hh => hcont (by rwa [schurEntry_symm hA] at hh)




/-- Both vertices of an `AfterIn` pair occur in the list. -/
theorem afterIn_mem {τ : List (Fin n)} {p x : Fin n} (h : AfterIn τ p x) :
    p ∈ τ ∧ x ∈ τ := by
  obtain ⟨l₁, l₂, l₃, hl⟩ := h
  subst hl
  constructor <;> simp



/-- Dropping the last pivot of an enumeration. -/
theorem enumerates_of_enumerates_append_singleton {lS : List (Fin n)}
    {S : Finset (Fin n)} {p : Fin n}
    (henum : Enumerates (lS ++ [p]) (insert p S)) (hp : p ∉ S) :
    Enumerates lS S := by
  obtain ⟨hnd, hto⟩ := henum
  have hndl : lS.Nodup := (List.nodup_append.mp hnd).1
  have hpnot : p ∉ lS := by
    intro hpL
    have hdisj := (List.nodup_append.mp hnd).2.2
    exact hdisj _ hpL _ (by simp) rfl
  refine ⟨hndl, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxp : x = p
    · subst hxp
      exact absurd (List.mem_toFinset.mp hx) hpnot
    · have hmem : x ∈ (lS ++ [p]).toFinset := by
        rw [List.mem_toFinset, List.mem_append]
        exact Or.inl (List.mem_toFinset.mp hx)
      rw [hto] at hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact absurd h hxp
      · exact h
  · intro hx
    have hmem : x ∈ (lS ++ [p]).toFinset := by
      rw [hto]
      exact Finset.mem_insert_of_mem hx
    rw [List.mem_toFinset, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with h | h
    · exact List.mem_toFinset.mpr h
    · exact absurd (h ▸ hx) hp



/-- One clean pivot prepends to a clean continuation: if `p` is clean
at level `S` and the level `insert p S` admits a clean continuation,
so does level `S`. This is the recursion step consumed by every
class in paper Theorem 4.8. -/
theorem admitsCleanContinuation_cons {A : Matrix (Fin n) (Fin n) ℝ}
    {lS : List (Fin n)} {S : Finset (Fin n)} {p : Fin n} (hp : p ∉ S)
    (hclean : ∀ x : Fin n, x ∉ S → x ≠ p →
      (gameGraph (patternGraph A) lS).Adj p x → schurEntry A S p x ≠ 0)
    (hnext : AdmitsCleanContinuation A (lS ++ [p]) (insert p S)) :
    AdmitsCleanContinuation A lS S := by
  classical
  obtain ⟨henum', τ', hτ'nd, hτ'mem, hτ'⟩ := hnext
  refine ⟨enumerates_of_enumerates_append_singleton henum' hp,
    p :: τ', ?_, ?_, ?_⟩
  · refine List.nodup_cons.mpr ⟨?_, hτ'nd⟩
    intro h
    exact (hτ'mem p).mp h (Finset.mem_insert_self p S)
  · intro x
    constructor
    · intro hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hp
      · have h2 := (hτ'mem x).mp hx
        exact fun h => h2 (Finset.mem_insert_of_mem h)
    · intro hx
      by_cases hxp : x = p
      · subst hxp
        simp
      · refine List.mem_cons_of_mem _ ((hτ'mem x).mpr ?_)
        simp [hxp, hx]
  · intro q x hAfter hAdj
    by_cases hqp : q = p
    · rw [hqp] at hAfter hAdj ⊢
      have hpre : prefixListBefore (p :: τ') p = [] := by
        simp [prefixListBefore]
      rw [hpre] at hAdj ⊢
      simp only [List.append_nil, List.toFinset_nil, Finset.union_empty]
        at hAdj ⊢
      have hxmem : x ∈ τ' := by
        have h2 := (afterIn_mem hAfter).2
        rcases List.mem_cons.mp h2 with hh | hh
        · exact absurd hh.symm hAdj.ne
        · exact hh
      have hxS : x ∉ S := by
        have h2 := (hτ'mem x).mp hxmem
        exact fun h => h2 (Finset.mem_insert_of_mem h)
      exact hclean x hxS (Ne.symm hAdj.ne) hAdj
    · have hAfter' : AfterIn τ' q x := by
        obtain ⟨l₁, l₂, l₃, hl⟩ := hAfter
        cases l₁ with
        | nil =>
            have h2 : p :: τ' = q :: (l₂ ++ x :: l₃) := by
              simpa using hl
            exact absurd (List.cons.inj h2).1.symm hqp
        | cons y l₁ =>
            have h2 : p :: τ' = y :: ((l₁ ++ q :: l₂) ++ x :: l₃) := by
              simpa using hl
            exact ⟨l₁, l₂, l₃, (List.cons.inj h2).2⟩
      have hpre : prefixListBefore (p :: τ') q
          = p :: prefixListBefore τ' q := by
        rw [prefixListBefore, prefixListBefore, List.takeWhile_cons]
        simp [Ne.symm hqp]
      rw [hpre] at hAdj ⊢
      have hset : S ∪ (p :: prefixListBefore τ' q).toFinset
          = insert p S ∪ (prefixListBefore τ' q).toFinset := by
        ext y
        simp only [List.toFinset_cons, Finset.mem_insert,
          Finset.mem_union, List.mem_toFinset]
        tauto
      rw [hset]
      apply hτ' q x hAfter'
      have hlist : (lS ++ [p]) ++ prefixListBefore τ' q
          = lS ++ (p :: prefixListBefore τ' q) := by
        rw [List.append_assoc]
        rfl
      rwa [hlist]

end CholeskyCancellations

/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.TakeWhile
import Section_4_PositiveResults.H_OneTriangleSetup

/-! # One-triangle continuation (paper Section 4)

The one-triangle state machine, clean apexes, and the per-matrix one-triangle class theorem (`one_triangle_perMatrix`, Theorem 4.8). Split from `Positives.lean`.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as `Defs.lean`; graph classes are predicates on `SimpleGraph (Fin n)` patterns and cleanliness is quantified per SPD realization through `PatternAdmitsPerMatrixCleanOrdering`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}




/-- `IsOneTriangleState A lS S T`: `(S, T)` is a one-triangle state —
at the level `S` (enumerated by `lS`) no fill or cancellation has
occurred yet (the game graph and the numeric pattern on survivors
both agree with `patternGraph A`), and the triangle `T` is still
entirely among the survivors. State for the induction proving paper
Theorem 4.8 (ii), `thm:positives`. -/
def IsOneTriangleState (A : Matrix (Fin n) (Fin n) ℝ)
    (lS : List (Fin n)) (S : Finset (Fin n)) (T : Finset (Fin n)) :
    Prop :=
  Enumerates lS S ∧ (∀ t ∈ T, t ∉ S) ∧
    (∀ x y : Fin n, x ∉ S → y ∉ S → x ≠ y →
      ((gameGraph (patternGraph A) lS).Adj x y ↔
        (patternGraph A).Adj x y)) ∧
    (∀ x y : Fin n, x ∉ S → y ∉ S → x ≠ y →
      (schurEntry A S x y ≠ 0 ↔ (patternGraph A).Adj x y))



/-- Clean apex in a numeric triangle: among three survivors with
pairwise nonzero entries, some apex leaves the opposite pair
nonzero after elimination (one application of the exchange step
`pivotEntry_ne_of_eq_zero`). -/
theorem exists_clean_apex {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {S : Finset (Fin n)} {x y z : Fin n}
    (hx : x ∉ S) (hy : y ∉ S) (hz : z ∉ S)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxz' : schurEntry A S x z ≠ 0) :
    pivotEntry A S x y z ≠ 0 ∨ pivotEntry A S y x z ≠ 0 := by
  by_cases h1 : pivotEntry A S x y z = 0
  · exact Or.inr
      (pivotEntry_ne_of_eq_zero hA S hx hy hz hxy hxz hyz hxz' h1)
  · exact Or.inl h1



/-- Finish a one-triangle state from a clean apex `v` of the
surviving triangle `{v, x₀, y₀}`: peel `v` as a clean simplicial
pair, then peel the remaining two vertices. -/
theorem one_triangle_finish_from_apex {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {lS : List (Fin n)} {S T : Finset (Fin n)}
    (hstate : IsOneTriangleState A lS S T)
    (hsurv : ∀ x : Fin n, x ∉ S → x ∈ T)
    {v x₀ y₀ : Fin n} (hv : v ∉ S) (hx₀ : x₀ ∉ S) (hy₀ : y₀ ∉ S)
    (hvx : v ≠ x₀) (hvy : v ≠ y₀) (hxy : x₀ ≠ y₀)
    (hT3 : ∀ x ∈ T, x = v ∨ x = x₀ ∨ x = y₀)
    (hadjxy : (patternGraph A).Adj x₀ y₀)
    (hex : schurEntry A S v x₀ ≠ 0) (hey : schurEntry A S v y₀ ≠ 0)
    (hafter : schurEntry A (insert v S) x₀ y₀ ≠ 0) :
    AdmitsCleanContinuation A lS S := by
  classical
  obtain ⟨henum, hTS, hgadj, hentry⟩ := hstate
  have hsurv3 : ∀ x : Fin n, x ∉ S → x = v ∨ x = x₀ ∨ x = y₀ :=
    fun x hx => hT3 x (hsurv x hx)
  have hmem1 : ∀ x : Fin n, x ∉ insert v S → x ∉ S ∧ x ≠ v := by
    intro x hx
    exact ⟨fun h => hx (Finset.mem_insert_of_mem h),
      fun h => hx (h ▸ Finset.mem_insert_self v S)⟩
  have hN : ∀ x : Fin n, x ∉ S → x ≠ v →
      (gameGraph (patternGraph A) lS).Adj v x →
        x = x₀ ∨ x = y₀ := by
    intro x hxS hxv _
    rcases hsurv3 x hxS with h | h | h
    · exact absurd h hxv
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨hclean₁, -, -⟩ := peel_clean_simplicial_pair hA henum hv
    hx₀ hy₀ hvx hvy hxy hN ((hgadj x₀ y₀ hx₀ hy₀ hxy).mpr hadjxy)
    hex hey hafter
  have hv2 : x₀ ∉ insert v S := by
    rw [Finset.mem_insert]
    push Not
    exact ⟨Ne.symm hvx, hx₀⟩
  have hN₂ : ∀ x : Fin n, x ∉ insert v S → x ≠ x₀ →
      (gameGraph (patternGraph A) (lS ++ [v])).Adj x₀ x →
        x = y₀ := by
    intro x hxS₁ hxx _
    obtain ⟨hxS, hxv⟩ := hmem1 x hxS₁
    rcases hsurv3 x hxS with h | h | h
    · exact absurd h hxv
    · exact absurd h hxx
    · exact h
  obtain ⟨hclean₂, -, -⟩ := peel_singleton_neighbor hA
    (enumerates_append_singleton henum hv) hv2 hN₂ hafter
  have hv3 : y₀ ∉ insert x₀ (insert v S) := by
    rw [Finset.mem_insert, Finset.mem_insert]
    push Not
    exact ⟨Ne.symm hxy, Ne.symm hvy, hy₀⟩
  have hclean₃ : ∀ x : Fin n, x ∉ insert x₀ (insert v S) → x ≠ y₀ →
      (gameGraph (patternGraph A) ((lS ++ [v]) ++ [x₀])).Adj y₀ x →
      schurEntry A (insert x₀ (insert v S)) y₀ x ≠ 0 := by
    intro x hxS₂ hxy₀ _
    have hxS : x ∉ S := fun h => hxS₂
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have hxv : x ≠ v := fun h => hxS₂
      (Finset.mem_insert_of_mem (h ▸ Finset.mem_insert_self v S))
    have hxx : x ≠ x₀ := fun h => hxS₂
      (h ▸ Finset.mem_insert_self x₀ (insert v S))
    rcases hsurv3 x hxS with h | h | h
    · exact absurd h hxv
    · exact absurd h hxx
    · exact absurd h hxy₀
  have hall : ∀ x : Fin n,
      x ∈ insert y₀ (insert x₀ (insert v S)) := by
    intro x
    by_cases hxS : x ∈ S
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem hxS))
    · rcases hsurv3 x hxS with rfl | rfl | rfl
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_self _ _))
      · exact Finset.mem_insert_of_mem
          (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_self _ _
  have hfinal : AdmitsCleanContinuation A
      (((lS ++ [v]) ++ [x₀]) ++ [y₀])
      (insert y₀ (insert x₀ (insert v S))) := by
    refine ⟨enumerates_append_singleton
      (enumerates_append_singleton
        (enumerates_append_singleton henum hv) hv2) hv3,
      [], List.nodup_nil, ?_, ?_⟩
    · intro x
      exact ⟨fun h => absurd h List.not_mem_nil,
        fun h => absurd (hall x) h⟩
    · intro p x hAfter _
      obtain ⟨l₁, l₂, l₃, hl⟩ := hAfter
      have hlen := congrArg List.length hl
      simp only [List.length_nil, List.length_append,
        List.length_cons] at hlen
      omega
  exact admitsCleanContinuation_cons hv hclean₁
    (admitsCleanContinuation_cons hv2 hclean₂
      (admitsCleanContinuation_cons hv3 hclean₃ hfinal))



/-- Finish a one-triangle state whose survivors are exactly the
triangle: pick a clean apex by the exchange step, then peel. -/
theorem one_triangle_finish {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {lS : List (Fin n)} {S T : Finset (Fin n)}
    (hTcard : T.card = 3)
    (hTclq : (patternGraph A).IsClique (↑T : Set (Fin n)))
    (hstate : IsOneTriangleState A lS S T)
    (hsurv : ∀ x : Fin n, x ∉ S → x ∈ T) :
    AdmitsCleanContinuation A lS S := by
  classical
  obtain ⟨henum, hTS, hgadj, hentry⟩ := hstate
  obtain ⟨t₁, t₂, t₃, h12, h13, h23, hTeq⟩ :=
    Finset.card_eq_three.mp hTcard
  have ht₁T : t₁ ∈ T := by rw [hTeq]; simp
  have ht₂T : t₂ ∈ T := by rw [hTeq]; simp
  have ht₃T : t₃ ∈ T := by rw [hTeq]; simp
  have ht₁ : t₁ ∉ S := hTS t₁ ht₁T
  have ht₂ : t₂ ∉ S := hTS t₂ ht₂T
  have ht₃ : t₃ ∉ S := hTS t₃ ht₃T
  have hadj12 : (patternGraph A).Adj t₁ t₂ :=
    hTclq (Finset.mem_coe.mpr ht₁T) (Finset.mem_coe.mpr ht₂T) h12
  have hadj13 : (patternGraph A).Adj t₁ t₃ :=
    hTclq (Finset.mem_coe.mpr ht₁T) (Finset.mem_coe.mpr ht₃T) h13
  have hadj23 : (patternGraph A).Adj t₂ t₃ :=
    hTclq (Finset.mem_coe.mpr ht₂T) (Finset.mem_coe.mpr ht₃T) h23
  have e12 : schurEntry A S t₁ t₂ ≠ 0 :=
    (hentry t₁ t₂ ht₁ ht₂ h12).mpr hadj12
  have e13 : schurEntry A S t₁ t₃ ≠ 0 :=
    (hentry t₁ t₃ ht₁ ht₃ h13).mpr hadj13
  have e23 : schurEntry A S t₂ t₃ ≠ 0 :=
    (hentry t₂ t₃ ht₂ ht₃ h23).mpr hadj23
  have hT3 : ∀ x ∈ T, x = t₁ ∨ x = t₂ ∨ x = t₃ := by
    intro x hx
    rw [hTeq] at hx
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
  rcases exists_clean_apex hA ht₁ ht₂ ht₃ h12 h13 h23 e13 with hp | hp
  · have h2 : t₂ ∉ insert t₁ S := by
      rw [Finset.mem_insert]
      push Not
      exact ⟨Ne.symm h12, ht₂⟩
    have h3 : t₃ ∉ insert t₁ S := by
      rw [Finset.mem_insert]
      push Not
      exact ⟨Ne.symm h13, ht₃⟩
    have hafter : schurEntry A (insert t₁ S) t₂ t₃ ≠ 0 := by
      rw [schur_quotient hA S t₁ ht₁ t₂ t₃ h2 h3]
      exact hp
    exact one_triangle_finish_from_apex hA ⟨henum, hTS, hgadj, hentry⟩ hsurv ht₁ ht₂ ht₃
      h12 h13 h23 hT3 hadj23 e12 e13 hafter
  · have e21 : schurEntry A S t₂ t₁ ≠ 0 := by
      rw [schurEntry_symm hA S t₂ t₁]
      exact e12
    have hT3' : ∀ x ∈ T, x = t₂ ∨ x = t₁ ∨ x = t₃ := by
      intro x hx
      rcases hT3 x hx with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    have h1' : t₁ ∉ insert t₂ S := by
      rw [Finset.mem_insert]
      push Not
      exact ⟨h12, ht₁⟩
    have h3' : t₃ ∉ insert t₂ S := by
      rw [Finset.mem_insert]
      push Not
      exact ⟨Ne.symm h23, ht₃⟩
    have hafter : schurEntry A (insert t₂ S) t₁ t₃ ≠ 0 := by
      rw [schur_quotient hA S t₂ ht₂ t₁ t₃ h1' h3']
      exact hp
    exact one_triangle_finish_from_apex hA ⟨henum, hTS, hgadj, hentry⟩ hsurv ht₂ ht₁ ht₃
      (Ne.symm h12) h23 h13 hT3' hadj13 e21 e23 hafter



/-- **One-triangle continuation.** From a one-triangle state there
is a clean continuation: while survivors outside the triangle
remain, peel the vertex given by `exists_peel_vertex` (at most one
survivor neighbour, so the pivot is clean and neither the game
graph nor any entry changes); when only the triangle remains,
finish by `one_triangle_finish`. -/
theorem one_triangle_continuation {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    ∀ (m : ℕ) {lS : List (Fin n)} {S T : Finset (Fin n)},
      ((Finset.univ \ S) \ T).card ≤ m →
      IsChordal (patternGraph A) → T.card = 3 →
      (patternGraph A).IsClique (↑T : Set (Fin n)) →
      (∀ T' : Finset (Fin n), T'.card = 3 →
        (patternGraph A).IsClique (↑T' : Set (Fin n)) → T' = T) →
      IsOneTriangleState A lS S T →
      AdmitsCleanContinuation A lS S := by
  intro m
  induction m with
  | zero =>
      intro lS S T hcard hG hTcard hTclq huni hstate
      refine one_triangle_finish hA hTcard hTclq hstate ?_
      intro x hxS
      have hempty : ((Finset.univ \ S) \ T) = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      by_contra hxT
      have hxmem : x ∈ ((Finset.univ \ S) \ T) := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact ⟨hxS, hxT⟩
      rw [hempty] at hxmem
      exact Finset.notMem_empty x hxmem
  | succ m ih =>
      intro lS S T hcard hG hTcard hTclq huni hstate
      obtain ⟨henum, hTS, hgadj, hentry⟩ := hstate
      by_cases hne : ((Finset.univ \ S) \ T).Nonempty
      · obtain ⟨v, hvU, u, hu⟩ := exists_peel_vertex hG huni hTclq hne
        obtain ⟨hvR, hvT⟩ := Finset.mem_sdiff.mp hvU
        have hvS : v ∉ S := (Finset.mem_sdiff.mp hvR).2
        have hgame_of : ∀ x : Fin n, x ∉ S → x ≠ v →
            (gameGraph (patternGraph A) lS).Adj v x →
            (patternGraph A).Adj v x :=
          fun x hxS hxv h => (hgadj v x hvS hxS (Ne.symm hxv)).mp h
        obtain ⟨u', hN, hentry'⟩ :
            ∃ u' : Fin n, (∀ x : Fin n, x ∉ S → x ≠ v →
                (gameGraph (patternGraph A) lS).Adj v x → x = u') ∧
              schurEntry A S v u' ≠ 0 := by
          by_cases hex : ∃ y : Fin n, y ∈ Finset.univ \ S ∧ y ≠ v ∧
              (patternGraph A).Adj v y
          · obtain ⟨y₀, hy₀R, hy₀v, hAdj₀⟩ := hex
            have hy₀u : y₀ = u := hu y₀ hy₀R hy₀v hAdj₀
            have huS : u ∉ S := hy₀u ▸ (Finset.mem_sdiff.mp hy₀R).2
            have huv : u ≠ v := hy₀u ▸ hy₀v
            have hAdjU : (patternGraph A).Adj v u := hy₀u ▸ hAdj₀
            refine ⟨u, ?_,
              (hentry v u hvS huS (Ne.symm huv)).mpr hAdjU⟩
            intro x hxS hxv hgame
            exact hu x
              (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxS⟩)
              hxv (hgame_of x hxS hxv hgame)
          · refine ⟨v, ?_, ne_of_gt (schurEntry_pos hA S hvS)⟩
            intro x hxS hxv hgame
            exact absurd ⟨x, Finset.mem_sdiff.mpr
              ⟨Finset.mem_univ x, hxS⟩, hxv,
              hgame_of x hxS hxv hgame⟩ hex
        obtain ⟨hclean, hent'', hgame''⟩ :=
          peel_singleton_neighbor hA henum hvS hN hentry'
        refine admitsCleanContinuation_cons hvS hclean ?_
        have hcardeq : (Finset.univ \ insert v S) \ T
            = ((Finset.univ \ S) \ T) \ {v} := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_univ,
            Finset.mem_insert, Finset.mem_singleton, true_and,
            not_or]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩
            exact ⟨⟨h2, h3⟩, h1⟩
          · rintro ⟨⟨h2, h3⟩, h1⟩
            exact ⟨⟨h1, h2⟩, h3⟩
        have hcard' : ((Finset.univ \ insert v S) \ T).card ≤ m := by
          rw [hcardeq, Finset.card_sdiff,
            Finset.singleton_inter_of_mem hvU,
            Finset.card_singleton]
          omega
        refine ih hcard' hG hTcard hTclq huni ?_
        refine ⟨enumerates_append_singleton henum hvS, ?_, ?_, ?_⟩
        · intro t ht
          rw [Finset.mem_insert]
          push Not
          exact ⟨fun h => hvT (h ▸ ht), hTS t ht⟩
        · intro x y hx hy hxy
          have hxS : x ∉ S :=
            fun h => hx (Finset.mem_insert_of_mem h)
          have hyS : y ∉ S :=
            fun h => hy (Finset.mem_insert_of_mem h)
          exact (hgame'' x y hx hy hxy).trans
            (hgadj x y hxS hyS hxy)
        · intro x y hx hy hxy
          have hxS : x ∉ S :=
            fun h => hx (Finset.mem_insert_of_mem h)
          have hyS : y ∉ S :=
            fun h => hy (Finset.mem_insert_of_mem h)
          rw [hent'' x y hx hy hxy]
          exact hentry x y hxS hyS hxy
      · refine one_triangle_finish hA hTcard hTclq
          ⟨henum, hTS, hgadj, hentry⟩ ?_
        intro x hxS
        by_contra hxT
        exact hne ⟨x, by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact ⟨hxS, hxT⟩⟩



/-- Chordal graphs with exactly one triangle admit per-matrix clean
orderings (paper Theorem 4.8 (ii), `thm:positives`, in its
per-matrix form; not the paper's strategy form). -/
theorem one_triangle_perMatrix {G : SimpleGraph (Fin n)}
    (hG : IsChordal G) (hone : ExactlyOneTriangle G) :
    PatternAdmitsPerMatrixCleanOrdering G := by
  intro A hA hpat
  have hone' : {T : Finset (Fin n) | T.card = 3 ∧
      G.IsClique (↑T : Set (Fin n))}.ncard = 1 := hone
  obtain ⟨T, hTset⟩ := Set.ncard_eq_one.mp hone'
  have hTmem : T ∈ {T' : Finset (Fin n) | T'.card = 3 ∧
      G.IsClique (↑T' : Set (Fin n))} := by
    rw [hTset]
    exact Set.mem_singleton T
  obtain ⟨hTcard, hTclq⟩ := hTmem
  have huniq : ∀ T' : Finset (Fin n), T'.card = 3 →
      G.IsClique (↑T' : Set (Fin n)) → T' = T := by
    intro T' h1 h2
    have hmem : T' ∈ {T'' : Finset (Fin n) | T''.card = 3 ∧
        G.IsClique (↑T'' : Set (Fin n))} := ⟨h1, h2⟩
    rw [hTset] at hmem
    exact Set.mem_singleton_iff.mp hmem
  apply exists_clean_of_continuation_empty hA
  refine one_triangle_continuation hA
    (((Finset.univ \ (∅ : Finset (Fin n))) \ T).card) le_rfl ?_
    hTcard ?_ ?_ ?_
  · rwa [hpat]
  · rwa [hpat]
  · intro T' h1 h2
    rw [hpat] at h2
    exact huniq T' h1 h2
  · refine ⟨⟨by simp, by simp⟩, ?_, ?_, ?_⟩
    · intro t ht
      simp
    · intro x y _ _ _
      exact Iff.rfl
    · intro x y _ _ hxy
      rw [schurEntry_empty]
      constructor
      · intro hne0
        exact patternGraph_adj_of_entry hxy hne0
      · intro hadj
        exact patternGraph_adj_entry hA hadj

end CholeskyCancellations

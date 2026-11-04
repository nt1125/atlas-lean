/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Algebra.Order.Star.Real
import Section_4_PositiveResults.J_EdgeDisjointAndAssembly

/-! # Adaptive strategies and fixed orderings for Theorem 4.8 (paper Section 4)

Paper Theorem 4.8 in the adaptive strategy sense of paper Definition 2.25
(`positives_adaptive`), obtained from the per-matrix form `positives` through the bridge
`perMatrix_implies_adaptiveStrategy`. Then the triangle part of paper Remark 4.9
(`positives_no_fixed_ordering`). The triangle `K₃` lies in every class of Theorem 4.8, and no
single ordering is clean for all its SPD realizations, so a clean strategy must read the matrix.
-/

open scoped Matrix

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as the Section 2 files;
graph classes are predicates on `SimpleGraph (Fin n)` patterns, and the triangle witness is a
concrete matrix on `Fin 3`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}



/-- **Theorem 4.8, strategy form** (paper Theorem 4.8, `thm:positives`, read through paper
Definition 2.25, `def:strategy`): each class admits an adaptive clean strategy, one pivot rule
that reads only the current level and Schur complement. This follows from `positives` by
`perMatrix_implies_adaptiveStrategy`. Strips, fans and one-triangle graphs have vertices by
definition. The edge-disjoint class also contains the graph on `Fin 0`, where no pivot rule
exists (`not_patternAdmitsAdaptiveStrategy_zero`), hence its hypothesis `0 < n`. -/
theorem positives_adaptive :
    (∀ {n : ℕ} (G : SimpleGraph (Fin n)), IsStripPattern G →
      PatternAdmitsAdaptiveStrategy G)
    ∧ (∀ {n : ℕ} (G : SimpleGraph (Fin n)), IsFanPattern G →
        PatternAdmitsAdaptiveStrategy G)
    ∧ (∀ {n : ℕ} (G : SimpleGraph (Fin n)),
        IsChordal G → ExactlyOneTriangle G → PatternAdmitsAdaptiveStrategy G)
    ∧ (∀ {n : ℕ} (G : SimpleGraph (Fin n)), 0 < n →
        IsChordal G → G.cliqueNum ≤ 3 → TrianglesEdgeDisjoint G →
          PatternAdmitsAdaptiveStrategy G) := by
  refine ⟨fun {n} G hG => ?_, fun {n} G hG => ?_, fun {n} G h₁ h₂ => ?_,
    fun {n} G hn h₁ h₂ h₃ => ?_⟩
  · have hn : 0 < n := by
      have := hG.1
      omega
    exact perMatrix_implies_adaptiveStrategy hn (positives.1 G hG)
  · have hn : 0 < n := by
      obtain ⟨c, -⟩ := hG
      exact Fin.pos c
    exact perMatrix_implies_adaptiveStrategy hn (positives.2.1 G hG)
  · have hn : 0 < n := by
      have hcard : {T : Finset (Fin n) | T.card = 3 ∧
          G.IsClique (↑T : Set (Fin n))}.ncard = 1 := h₂
      obtain ⟨T, hT⟩ := Set.nonempty_of_ncard_ne_zero (s := {T : Finset (Fin n) |
        T.card = 3 ∧ G.IsClique (↑T : Set (Fin n))}) (by omega)
      have hT3 : T.card = 3 := hT.1
      have hle := T.card_le_univ
      rw [Fintype.card_fin] at hle
      omega
    exact perMatrix_implies_adaptiveStrategy hn (positives.2.2.1 G h₁ h₂)
  · exact perMatrix_implies_adaptiveStrategy hn (positives.2.2.2 G h₁ h₂ h₃)



/-- `triangleWitness a`: an SPD realization of the triangle `K₃` (paper Remark 4.9). It has unit
diagonal, `1/2` on the two entries at `a` and `1/4` on the opposite entry. Pivoting `a` cancels
the opposite entry, since `1/4 - (1/2)(1/2)/1 = 0`. -/
noncomputable def triangleWitness (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if i = j then 1 else if i = a ∨ j = a then 1 / 2 else 1 / 4



/-- `triangleFactor a`: the unit lower-triangular factor of `triangleWitness a` for an ordering
that starts with `a`. It has ones on the diagonal and `1/2` below them in column `a`. -/
noncomputable def triangleFactor (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if i = j then 1 else if j = a then 1 / 2 else 0



/-- `triangleWitness a` is positive definite, by the `L D Lᵀ` congruence with `L` the factor
`triangleFactor a` and pivots `1` at `a` and `3/4` elsewhere. -/
theorem triangleWitness_posDef (a : Fin 3) : (triangleWitness a).PosDef := by
  have hdet : IsUnit (triangleFactor a).det := by
    fin_cases a <;> norm_num [Matrix.det_fin_three, triangleFactor]
  have hunit : IsUnit (triangleFactor a) := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hD : (Matrix.diagonal fun i : Fin 3 => if i = a then (1 : ℝ) else 3 / 4).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    split_ifs <;> norm_num
  have hcong := hD.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hunit)
  have hfact : triangleWitness a = triangleFactor a *
      Matrix.diagonal (fun i : Fin 3 => if i = a then (1 : ℝ) else 3 / 4) *
        (triangleFactor a)ᴴ := by
    have ht : (triangleFactor a)ᴴ = (triangleFactor a)ᵀ := by
      ext i j
      simp [Matrix.conjTranspose]
    rw [ht]
    ext i j
    fin_cases a <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.mul_diagonal, triangleWitness, triangleFactor,
        Fin.sum_univ_three]
  rwa [hfact]



/-- `triangleWitness a` realizes the triangle: all its off-diagonal entries are nonzero. -/
theorem patternGraph_triangleWitness (a : Fin 3) : patternGraph (triangleWitness a) = ⊤ := by
  ext i j
  simp only [patternGraph, SimpleGraph.fromRel_adj, SimpleGraph.top_adj]
  constructor
  · exact fun h => h.1
  · intro hij
    refine ⟨hij, Or.inl ?_⟩
    simp only [triangleWitness, Matrix.of_apply, hij, ↓reduceIte]
    split_ifs <;> norm_num



/-- Pivoting `a` first in `triangleWitness a` cancels the entry between the other two vertices
(paper Remark 4.9). -/
theorem triangleWitness_schur_opposite {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : schurEntry (triangleWitness a) {a} b c = 0 := by
  have hb : b ∉ insert a (∅ : Finset (Fin 3)) := by simpa using hab.symm
  have hc : c ∉ insert a (∅ : Finset (Fin 3)) := by simpa using hac.symm
  have h := schur_quotient (triangleWitness_posDef a) ∅ a (Finset.notMem_empty a) b c hb hc
  rw [insert_empty_eq] at h
  rw [h, pivotEntry, schurEntry_empty, schurEntry_empty, schurEntry_empty, schurEntry_empty]
  simp only [triangleWitness, Matrix.of_apply]
  norm_num [hbc, hab.symm, hac.symm]



/-- **No fixed ordering for the triangle** (paper Remark 4.9): whatever ordering `[a, b, c]` is
fixed in advance, the realization `triangleWitness a` cancels the predicted-nonzero entry
`{b, c}` at its committing level `{a}`. -/
theorem triangle_no_fixed_ordering (σ : List (Fin 3)) :
    ¬ IsFixedOrderingFor (⊤ : SimpleGraph (Fin 3)) σ := by
  rintro ⟨⟨hnd, hlen⟩, hclean⟩
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c : Fin 3, σ = [a, b, c] := by
    rcases σ with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, σ⟩⟩⟩⟩
    · simp only [List.length_nil] at hlen
      omega
    · simp only [List.length_cons, List.length_nil] at hlen
      omega
    · simp only [List.length_cons, List.length_nil] at hlen
      omega
    · exact ⟨a, b, c, rfl⟩
    · simp only [List.length_cons] at hlen
      omega
  have hab : a ≠ b := fun h => by subst h; simp at hnd
  have hac : a ≠ c := fun h => by subst h; simp at hnd
  have hbc : b ≠ c := fun h => by subst h; simp at hnd
  have hadj : (patternGraph (triangleWitness a)).Adj b c := by
    rw [patternGraph_triangleWitness]
    exact (SimpleGraph.top_adj b c).mpr hbc
  have hpred : PredictedNonzero (triangleWitness a) [a, b, c] b c :=
    patternGraph_le_fillGraph (triangleWitness a) [a, b, c] hadj
  have h := hclean (triangleWitness a) (triangleWitness_posDef a)
    (patternGraph_triangleWitness a) b c hpred
  have hpre : prefixSet [a, b, c] b c = {a} := by
    rw [prefixSet, prefixList_of_split (σ := [a, b, c]) (l₁ := [a]) (p := b) (l₂ := [c]) rfl
      (by simpa using hab.symm) (by simpa using hac.symm)]
    simp
  rw [hpre] at h
  exact h (triangleWitness_schur_opposite hab hac hbc)



/-- The triangle is a 2-path strip, on the list `[0, 1, 2]` (paper Definition 4.3). -/
theorem top_isStripPattern : IsStripPattern (⊤ : SimpleGraph (Fin 3)) := by
  refine ⟨le_rfl, [0, 1, 2], ⟨by decide, rfl⟩, fun x y => ?_⟩
  rw [SimpleGraph.top_adj]
  constructor
  · intro hxy
    fin_cases x <;> fin_cases y
    all_goals first
      | exact absurd rfl hxy
      | exact Or.inl (Or.inl ⟨[], [2], rfl⟩)
      | exact Or.inl (Or.inr ⟨[], [2], rfl⟩)
      | exact Or.inl (Or.inl ⟨[0], [], rfl⟩)
      | exact Or.inl (Or.inr ⟨[0], [], rfl⟩)
      | exact Or.inr (Or.inl ⟨[], [], 1, rfl⟩)
      | exact Or.inr (Or.inr ⟨[], [], 1, rfl⟩)
  · rintro (h | h)
    · exact distOneIn_ne (by decide) h
    · exact distTwoIn_ne (by decide) h



/-- The triangle is a dominating-vertex fan, with center `0` and path `[1, 2]` (paper
Theorem 4.8 (i)). -/
theorem top_isFanPattern : IsFanPattern (⊤ : SimpleGraph (Fin 3)) := by
  refine ⟨0, [1, 2], by decide, by decide, fun v hv => (SimpleGraph.top_adj 0 v).mpr hv.symm,
    fun x y hx hy => ?_⟩
  rw [SimpleGraph.top_adj]
  constructor
  · intro hxy
    fin_cases x <;> fin_cases y
    all_goals first
      | exact absurd rfl hx
      | exact absurd rfl hy
      | exact absurd rfl hxy
      | exact Or.inl ⟨[], [], rfl⟩
      | exact Or.inr ⟨[], [], rfl⟩
  · exact fun h => distOneIn_ne (by decide) h



/-- The triangle is chordal: `[0, 1, 2]` is a perfect elimination ordering, since every vertex
set is a clique of `⊤` (paper Definition 2.14). -/
theorem top_isChordal : IsChordal (⊤ : SimpleGraph (Fin 3)) := by
  refine isChordal_of_isPerfectEliminationOrdering (σ := [0, 1, 2]) ⟨⟨by decide, rfl⟩, fun j => ?_⟩
  intro x _ y _ hxy
  exact (SimpleGraph.top_adj x y).mpr hxy



/-- The triangle has exactly one triangle, the whole vertex set (paper Theorem 4.8 (ii)). -/
theorem top_exactlyOneTriangle : ExactlyOneTriangle (⊤ : SimpleGraph (Fin 3)) := by
  have hset : {T : Finset (Fin 3) | T.card = 3 ∧
      (⊤ : SimpleGraph (Fin 3)).IsClique (↑T : Set (Fin 3))} = {Finset.univ} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hcard, -⟩
      exact (Finset.card_eq_iff_eq_univ T).mp (by simpa using hcard)
    · rintro rfl
      refine ⟨by simp, ?_⟩
      intro x _ y _ hxy
      exact (SimpleGraph.top_adj x y).mpr hxy
  rw [ExactlyOneTriangle, hset, Set.ncard_singleton]



/-- The triangle has clique number `3` (paper Theorem 4.8 (iii)). -/
theorem top_cliqueNum_le : (⊤ : SimpleGraph (Fin 3)).cliqueNum ≤ 3 := by
  rw [SimpleGraph.cliqueNum_top]
  simp



/-- The triangle's triangles are pairwise edge-disjoint, vacuously, since it has only one
(paper Theorem 4.8 (iii)). -/
theorem top_trianglesEdgeDisjoint : TrianglesEdgeDisjoint (⊤ : SimpleGraph (Fin 3)) := by
  intro T₁ T₂ h₁ _ h₂ _ hne
  exfalso
  apply hne
  rw [(Finset.card_eq_iff_eq_univ T₁).mp (by simpa using h₁),
    (Finset.card_eq_iff_eq_univ T₂).mp (by simpa using h₂)]



/-- **No fixed ordering suffices for any class of Theorem 4.8** (paper Remark 4.9). The triangle
`K₃` is a strip, a fan, a chordal graph with exactly one triangle, and a chordal graph with
`ω ≤ 3` and edge-disjoint triangles. No ordering is clean for all its SPD realizations
(`triangle_no_fixed_ordering`). So the strategies of `positives_adaptive` must depend on the
matrix and not only on the pattern. -/
theorem positives_no_fixed_ordering :
    IsStripPattern (⊤ : SimpleGraph (Fin 3)) ∧ IsFanPattern (⊤ : SimpleGraph (Fin 3))
    ∧ (IsChordal (⊤ : SimpleGraph (Fin 3)) ∧ ExactlyOneTriangle (⊤ : SimpleGraph (Fin 3)))
    ∧ (IsChordal (⊤ : SimpleGraph (Fin 3)) ∧ (⊤ : SimpleGraph (Fin 3)).cliqueNum ≤ 3
        ∧ TrianglesEdgeDisjoint (⊤ : SimpleGraph (Fin 3)))
    ∧ ∀ σ : List (Fin 3), ¬ IsFixedOrderingFor (⊤ : SimpleGraph (Fin 3)) σ :=
  ⟨top_isStripPattern, top_isFanPattern, ⟨top_isChordal, top_exactlyOneTriangle⟩,
    ⟨top_isChordal, top_cliqueNum_le, top_trianglesEdgeDisjoint⟩, triangle_no_fixed_ordering⟩

end CholeskyCancellations

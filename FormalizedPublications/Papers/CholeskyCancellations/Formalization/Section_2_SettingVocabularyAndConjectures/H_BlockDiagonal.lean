/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Section_2_SettingVocabularyAndConjectures.G_FillGraphChordal
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Block-diagonal matrices (paper Section 2)

Why irreducibility is harmless (paper Remark 2.18, `rem:irred-harmless`): if `A` is block
diagonal, clean orderings of the blocks concatenate to a clean ordering of `A`
(`blockDiag_isCleanOrdering`, `blockDiag_exists_clean`), and the fill graph of the
concatenated ordering is the disjoint union of the blocks' fill graphs
(`blockDiag_fillGraph`).

Modelling choice: "block diagonal" is formalised literally as the matrix
`blockDiag A₁ A₂ = diag(A₁, A₂)` on `Fin (n₁ + n₂)` (Mathlib's `Matrix.fromBlocks A₁ 0 0 A₂`
reindexed along `finSumFinEquiv`): the first block occupies the indices `Fin.castAdd n₂ j`,
the second the indices `Fin.natAdd n₁ k`, and `blockOrdering σ₁ σ₂` pivots through the first
block (in the order `σ₁`) before the second (in the order `σ₂`). An arbitrary reducible
matrix (paper Definition 2.16, `def:irred`) is a symmetric permutation of such a matrix, and
more than two blocks are reached by iterating. Gap: the transport of fill graphs and clean
orderings along a symmetric permutation is not formalized here, so the remark is proved for
the literal block-diagonal form.

The proofs follow the paper. Fill: by the fill-path theorem (paper Proposition 2.10,
`fill_path`) a fill edge is a path of `G_A` through earlier pivots, and a path of `G_A` never
leaves its block (`block_walk_pullback`). Cleanliness: every Schur complement of
`diag(A₁, A₂)` is again block diagonal, its blocks being the Schur complements of `A₁` and
`A₂` at the two parts of the level (`block_schurEntry_castAdd_castAdd`,
`block_schurEntry_natAdd_natAdd`, by induction on the level through the quotient property of
paper Lemma 2.4).
-/

open scoped Matrix

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): vertices `Fin n`, SPD = `Matrix.PosDef`,
levels `Finset (Fin n)`, pivot-order list orderings, Schur entries through `schurEntry` only.
(Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- The block-diagonal matrix `diag(A₁, A₂)` on `Fin (n₁ + n₂)` (first block first), the
block-diagonal `A` of paper Remark 2.18 (`rem:irred-harmless`): Mathlib's
`Matrix.fromBlocks A₁ 0 0 A₂` reindexed along `finSumFinEquiv`, so the first block sits on
the indices `Fin.castAdd n₂ j` and the second on the indices `Fin.natAdd n₁ k`. -/
noncomputable def blockDiag {n₁ n₂ : ℕ} (A₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (A₂ : Matrix (Fin n₂) (Fin n₂) ℝ) : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A₁ 0 0 A₂)



/-- The concatenation of an ordering of the first block with one of the second (paper
Remark 2.18, `rem:irred-harmless`: "a clean ordering for each block concatenates to a clean
ordering for `A`"). -/
def blockOrdering {n₁ n₂ : ℕ} (σ₁ : List (Fin n₁)) (σ₂ : List (Fin n₂)) :
    List (Fin (n₁ + n₂)) :=
  σ₁.map (Fin.castAdd n₂) ++ σ₂.map (Fin.natAdd n₁)



/-- The two blocks of `Fin (n₁ + n₂)` are disjoint: a first-block index is never a
second-block index (paper Remark 2.18, `rem:irred-harmless`). -/
theorem block_castAdd_ne_natAdd {n₁ n₂ : ℕ} (j : Fin n₁) (k : Fin n₂) :
    Fin.castAdd n₂ j ≠ Fin.natAdd n₁ k := by
  intro h
  have hval := congrArg Fin.val h
  have hj := j.isLt
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  omega



/-- The two blocks of `Fin (n₁ + n₂)` are disjoint, second block first (paper Remark 2.18,
`rem:irred-harmless`). -/
theorem block_natAdd_ne_castAdd {n₁ n₂ : ℕ} (k : Fin n₂) (j : Fin n₁) :
    Fin.natAdd n₁ k ≠ Fin.castAdd n₂ j :=
  (block_castAdd_ne_natAdd j k).symm



/-- Every index of `Fin (n₁ + n₂)` lies in the first or in the second block (paper
Remark 2.18, `rem:irred-harmless`). -/
theorem block_cases {n₁ n₂ : ℕ} (u : Fin (n₁ + n₂)) :
    (∃ j : Fin n₁, u = Fin.castAdd n₂ j) ∨ ∃ k : Fin n₂, u = Fin.natAdd n₁ k := by
  induction u using Fin.addCases with
  | left j => exact Or.inl ⟨j, rfl⟩
  | right k => exact Or.inr ⟨k, rfl⟩



/-- Entries of `diag(A₁, A₂)` inside the first block are entries of `A₁` (paper
Remark 2.18, `rem:irred-harmless`). -/
theorem blockDiag_apply_castAdd_castAdd {n₁ n₂ : ℕ} (A₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (A₂ : Matrix (Fin n₂) (Fin n₂) ℝ) (j k : Fin n₁) :
    blockDiag A₁ A₂ (Fin.castAdd n₂ j) (Fin.castAdd n₂ k) = A₁ j k := by
  simp [blockDiag, Matrix.reindex_apply]



/-- Entries of `diag(A₁, A₂)` from the first block to the second vanish (paper
Remark 2.18, `rem:irred-harmless`). -/
theorem blockDiag_apply_castAdd_natAdd {n₁ n₂ : ℕ} (A₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (A₂ : Matrix (Fin n₂) (Fin n₂) ℝ) (j : Fin n₁) (k : Fin n₂) :
    blockDiag A₁ A₂ (Fin.castAdd n₂ j) (Fin.natAdd n₁ k) = 0 := by
  simp [blockDiag, Matrix.reindex_apply]



/-- Entries of `diag(A₁, A₂)` from the second block to the first vanish (paper
Remark 2.18, `rem:irred-harmless`). -/
theorem blockDiag_apply_natAdd_castAdd {n₁ n₂ : ℕ} (A₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (A₂ : Matrix (Fin n₂) (Fin n₂) ℝ) (k : Fin n₂) (j : Fin n₁) :
    blockDiag A₁ A₂ (Fin.natAdd n₁ k) (Fin.castAdd n₂ j) = 0 := by
  simp [blockDiag, Matrix.reindex_apply]



/-- Entries of `diag(A₁, A₂)` inside the second block are entries of `A₂` (paper
Remark 2.18, `rem:irred-harmless`). -/
theorem blockDiag_apply_natAdd_natAdd {n₁ n₂ : ℕ} (A₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (A₂ : Matrix (Fin n₂) (Fin n₂) ℝ) (j k : Fin n₂) :
    blockDiag A₁ A₂ (Fin.natAdd n₁ j) (Fin.natAdd n₁ k) = A₂ j k := by
  simp [blockDiag, Matrix.reindex_apply]



/-- `diag(A₁, A₂)` is SPD when both blocks are (paper Remark 2.18, `rem:irred-harmless`;
SPD as in paper Definition 2.1): its quadratic form is the sum of the blocks' forms. -/
theorem blockDiag_posDef {n₁ n₂ : ℕ} {A₁ : Matrix (Fin n₁) (Fin n₁) ℝ}
    {A₂ : Matrix (Fin n₂) (Fin n₂) ℝ} (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) :
    (blockDiag A₁ A₂).PosDef := by
  have hfb : (Matrix.fromBlocks A₁ 0 0 A₂).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (Matrix.IsHermitian.fromBlocks hA₁.isHermitian (by simp) hA₂.isHermitian) ?_
    intro x hx
    have hsplit : star x ⬝ᵥ (Matrix.fromBlocks A₁ 0 0 A₂ *ᵥ x)
        = star (x ∘ Sum.inl) ⬝ᵥ (A₁ *ᵥ (x ∘ Sum.inl))
          + star (x ∘ Sum.inr) ⬝ᵥ (A₂ *ᵥ (x ∘ Sum.inr)) := by
      rw [Matrix.fromBlocks_mulVec, Matrix.dotProduct_block]
      simp
    rw [hsplit]
    have h₁ := hA₁.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have h₂ := hA₂.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    by_cases hl : x ∘ Sum.inl = 0
    · have hr : x ∘ Sum.inr ≠ 0 := by
        intro hr
        apply hx
        funext i
        cases i with
        | inl a => exact congr_fun hl a
        | inr b => exact congr_fun hr b
      have := hA₂.dotProduct_mulVec_pos hr
      linarith
    · have := hA₁.dotProduct_mulVec_pos hl
      linarith
  rw [blockDiag, Matrix.reindex_apply]
  exact hfb.submatrix finSumFinEquiv.symm.injective



/-- An ordering lists every vertex (paper Section 2's orderings `σ = (v₁, …, vₙ)`, used for
the committing prefixes of paper Remark 2.18, `rem:irred-harmless`). -/
theorem block_mem_of_isOrdering {σ : List (Fin n)} (hσ : IsOrdering σ) (x : Fin n) :
    x ∈ σ := by
  have h1 : σ.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hσ.1, hσ.2, Fintype.card_fin]
  exact List.mem_toFinset.mp (by rw [h1]; exact Finset.mem_univ x)



/-- The concatenation of orderings of the two blocks is an ordering of `Fin (n₁ + n₂)`
(paper Remark 2.18, `rem:irred-harmless`). -/
theorem blockOrdering_isOrdering {n₁ n₂ : ℕ} {σ₁ : List (Fin n₁)} {σ₂ : List (Fin n₂)}
    (hσ₁ : IsOrdering σ₁) (hσ₂ : IsOrdering σ₂) : IsOrdering (blockOrdering σ₁ σ₂) := by
  refine ⟨List.nodup_append.mpr ⟨hσ₁.1.map (Fin.castAdd_injective n₁ n₂),
    hσ₂.1.map (Fin.natAdd_injective n₂ n₁), ?_⟩, ?_⟩
  · intro a ha b hb
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hb
    exact block_castAdd_ne_natAdd j k
  · simp [blockOrdering, hσ₁.2, hσ₂.2]



/-- A committing prefix is decided inside an initial segment containing one endpoint (paper
Definitions 2.23 and 2.24's committing prefixes, for paper Remark 2.18,
`rem:irred-harmless`). -/
theorem block_prefixList_append_of_mem {l₁ : List (Fin n)} {j : Fin n} (hj : j ∈ l₁)
    (l₂ : List (Fin n)) (k : Fin n) :
    prefixList (l₁ ++ l₂) j k = prefixList l₁ j k := by
  induction l₁ with
  | nil => simp at hj
  | cons y l ih =>
    unfold prefixList at ih ⊢
    rw [List.cons_append, List.takeWhile_cons, List.takeWhile_cons]
    rcases List.mem_cons.mp hj with rfl | hj'
    · simp
    · rw [ih hj']



/-- A committing prefix runs through an initial segment avoiding both endpoints (paper
Definitions 2.23 and 2.24's committing prefixes, for paper Remark 2.18,
`rem:irred-harmless`). -/
theorem block_prefixList_append_of_notMem {l₁ : List (Fin n)} {j k : Fin n} (hj : j ∉ l₁)
    (hk : k ∉ l₁) (l₂ : List (Fin n)) :
    prefixList (l₁ ++ l₂) j k = l₁ ++ prefixList l₂ j k := by
  refine List.takeWhile_append_of_pos (fun x hx => ?_)
  simp only [decide_eq_true_eq]
  exact ⟨fun h => hj (h ▸ hx), fun h => hk (h ▸ hx)⟩



/-- Committing prefixes commute with an injective relabelling of the vertices (paper
Definitions 2.23 and 2.24's committing prefixes, for paper Remark 2.18,
`rem:irred-harmless`). -/
theorem block_prefixList_map {m N : ℕ} (f : Fin m → Fin N) (hf : Function.Injective f)
    (l : List (Fin m)) (j k : Fin m) :
    prefixList (l.map f) (f j) (f k) = (prefixList l j k).map f := by
  rw [prefixList, List.takeWhile_map]
  congr 1
  exact takeWhile_ext l _ _ (fun x => by simp [hf.eq_iff])



/-- The committing prefix of a first-block pair in `blockOrdering σ₁ σ₂` is the image of
its committing prefix in `σ₁` (paper Remark 2.18, `rem:irred-harmless`). -/
theorem block_prefixList_castAdd {n₁ n₂ : ℕ} {σ₁ : List (Fin n₁)} (hσ₁ : IsOrdering σ₁)
    (σ₂ : List (Fin n₂)) (j k : Fin n₁) :
    prefixList (blockOrdering σ₁ σ₂) (Fin.castAdd n₂ j) (Fin.castAdd n₂ k) =
      (prefixList σ₁ j k).map (Fin.castAdd n₂) := by
  rw [blockOrdering, block_prefixList_append_of_mem
      (List.mem_map_of_mem (block_mem_of_isOrdering hσ₁ j)),
    block_prefixList_map _ (Fin.castAdd_injective n₁ n₂)]



/-- The committing prefix of a second-block pair in `blockOrdering σ₁ σ₂` is all of the
first block followed by the image of its committing prefix in `σ₂` (paper Remark 2.18,
`rem:irred-harmless`). -/
theorem block_prefixList_natAdd {n₁ n₂ : ℕ} (σ₁ : List (Fin n₁)) (σ₂ : List (Fin n₂))
    (j k : Fin n₂) :
    prefixList (blockOrdering σ₁ σ₂) (Fin.natAdd n₁ j) (Fin.natAdd n₁ k) =
      σ₁.map (Fin.castAdd n₂) ++ (prefixList σ₂ j k).map (Fin.natAdd n₁) := by
  have hnot : ∀ x : Fin n₂, Fin.natAdd n₁ x ∉ σ₁.map (Fin.castAdd n₂) := by
    intro x hx
    obtain ⟨y, -, hy⟩ := List.mem_map.mp hx
    exact block_castAdd_ne_natAdd y x hy
  rw [blockOrdering, block_prefixList_append_of_notMem (hnot j) (hnot k),
    block_prefixList_map _ (Fin.natAdd_injective n₂ n₁)]



/-- The first-block part of the committing level of a first-block pair is its committing
level in `σ₁` (paper Remark 2.18, `rem:irred-harmless`). -/
theorem block_filter_prefixSet_castAdd {n₁ n₂ : ℕ} {σ₁ : List (Fin n₁)}
    (hσ₁ : IsOrdering σ₁) (σ₂ : List (Fin n₂)) (j k : Fin n₁) :
    (Finset.univ.filter fun x => Fin.castAdd n₂ x ∈
        prefixSet (blockOrdering σ₁ σ₂) (Fin.castAdd n₂ j) (Fin.castAdd n₂ k)) =
      prefixSet σ₁ j k := by
  ext x
  simp [prefixSet, block_prefixList_castAdd hσ₁, Fin.castAdd_inj]



/-- The second-block part of the committing level of a second-block pair is its committing
level in `σ₂` (paper Remark 2.18, `rem:irred-harmless`). -/
theorem block_filter_prefixSet_natAdd {n₁ n₂ : ℕ} (σ₁ : List (Fin n₁))
    (σ₂ : List (Fin n₂)) (j k : Fin n₂) :
    (Finset.univ.filter fun x => Fin.natAdd n₁ x ∈
        prefixSet (blockOrdering σ₁ σ₂) (Fin.natAdd n₁ j) (Fin.natAdd n₁ k)) =
      prefixSet σ₂ j k := by
  ext x
  simp [prefixSet, block_prefixList_natAdd, Fin.natAdd_inj, block_castAdd_ne_natAdd]



/-- The first endpoint survives at the committing level (paper Definitions 2.23 and 2.24,
as used in paper Remark 2.18, `rem:irred-harmless`). -/
theorem block_left_notMem_prefixSet (σ : List (Fin n)) (j k : Fin n) :
    j ∉ prefixSet σ j k := fun h =>
  (mem_prefixList_imp (List.mem_toFinset.mp h)).1 rfl



/-- The second endpoint survives at the committing level (paper Definitions 2.23 and 2.24,
as used in paper Remark 2.18, `rem:irred-harmless`). -/
theorem block_right_notMem_prefixSet (σ : List (Fin n)) (j k : Fin n) :
    k ∉ prefixSet σ j k := fun h =>
  (mem_prefixList_imp (List.mem_toFinset.mp h)).2 rfl



/-- Inside the first block, the disjoint union of `K₁` and `K₂` is `K₁` (paper
Remark 2.18, `rem:irred-harmless`: "the disjoint union of the blocks' fill graphs"). -/
theorem block_adj_castAdd_castAdd {n₁ n₂ : ℕ} (K₁ : SimpleGraph (Fin n₁))
    (K₂ : SimpleGraph (Fin n₂)) (j k : Fin n₁) :
    (K₁.map (Fin.castAddEmb n₂) ⊔ K₂.map (Fin.natAddEmb n₁)).Adj
      (Fin.castAdd n₂ j) (Fin.castAdd n₂ k) ↔ K₁.Adj j k := by
  rw [SimpleGraph.sup_adj, SimpleGraph.map_adj, SimpleGraph.map_adj]
  simp [Fin.castAdd_inj, block_natAdd_ne_castAdd]



/-- Inside the second block, the disjoint union of `K₁` and `K₂` is `K₂` (paper
Remark 2.18, `rem:irred-harmless`). -/
theorem block_adj_natAdd_natAdd {n₁ n₂ : ℕ} (K₁ : SimpleGraph (Fin n₁))
    (K₂ : SimpleGraph (Fin n₂)) (j k : Fin n₂) :
    (K₁.map (Fin.castAddEmb n₂) ⊔ K₂.map (Fin.natAddEmb n₁)).Adj
      (Fin.natAdd n₁ j) (Fin.natAdd n₁ k) ↔ K₂.Adj j k := by
  rw [SimpleGraph.sup_adj, SimpleGraph.map_adj, SimpleGraph.map_adj]
  simp [Fin.natAdd_inj, block_castAdd_ne_natAdd]



/-- No edge of the disjoint union of `K₁` and `K₂` crosses the blocks (paper Remark 2.18,
`rem:irred-harmless`). -/
theorem block_not_adj_castAdd_natAdd {n₁ n₂ : ℕ} (K₁ : SimpleGraph (Fin n₁))
    (K₂ : SimpleGraph (Fin n₂)) (j : Fin n₁) (k : Fin n₂) :
    ¬ (K₁.map (Fin.castAddEmb n₂) ⊔ K₂.map (Fin.natAddEmb n₁)).Adj
      (Fin.castAdd n₂ j) (Fin.natAdd n₁ k) := by
  rw [SimpleGraph.sup_adj, SimpleGraph.map_adj, SimpleGraph.map_adj]
  simp [block_castAdd_ne_natAdd, block_natAdd_ne_castAdd]



/-- Every neighbour of a first-block vertex lies in the first block (paper Remark 2.18,
`rem:irred-harmless`). -/
theorem block_closed_castAdd {n₁ n₂ : ℕ} (K₁ : SimpleGraph (Fin n₁))
    (K₂ : SimpleGraph (Fin n₂)) (a : Fin n₁) (y : Fin (n₁ + n₂))
    (h : (K₁.map (Fin.castAddEmb n₂) ⊔ K₂.map (Fin.natAddEmb n₁)).Adj
      (Fin.castAdd n₂ a) y) :
    ∃ b : Fin n₁, y = Fin.castAdd n₂ b := by
  rcases block_cases y with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact ⟨b, rfl⟩
  · exact absurd h (block_not_adj_castAdd_natAdd K₁ K₂ a b)



/-- Every neighbour of a second-block vertex lies in the second block (paper Remark 2.18,
`rem:irred-harmless`). -/
theorem block_closed_natAdd {n₁ n₂ : ℕ} (K₁ : SimpleGraph (Fin n₁))
    (K₂ : SimpleGraph (Fin n₂)) (a : Fin n₂) (y : Fin (n₁ + n₂))
    (h : (K₁.map (Fin.castAddEmb n₂) ⊔ K₂.map (Fin.natAddEmb n₁)).Adj
      (Fin.natAdd n₁ a) y) :
    ∃ b : Fin n₂, y = Fin.natAdd n₁ b := by
  rcases block_cases y with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact absurd h.symm (block_not_adj_castAdd_natAdd K₁ K₂ b a)
  · exact ⟨b, rfl⟩



/-- The pattern graph of `diag(A₁, A₂)` is the disjoint union of the blocks' pattern graphs
(paper Remark 2.18, `rem:irred-harmless`, with the pattern graph of paper Definition 2.7,
`def:fill`). -/
theorem blockDiag_patternGraph {n₁ n₂ : ℕ} (A₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (A₂ : Matrix (Fin n₂) (Fin n₂) ℝ) :
    patternGraph (blockDiag A₁ A₂) =
      (patternGraph A₁).map (Fin.castAddEmb n₂) ⊔
        (patternGraph A₂).map (Fin.natAddEmb n₁) := by
  ext u v
  rcases block_cases u with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    rcases block_cases v with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [block_adj_castAdd_castAdd]
    simp [patternGraph, SimpleGraph.fromRel_adj, blockDiag_apply_castAdd_castAdd,
      Fin.castAdd_inj]
  · refine iff_of_false ?_ (block_not_adj_castAdd_natAdd _ _ j k)
    simp [patternGraph, SimpleGraph.fromRel_adj, blockDiag_apply_castAdd_natAdd,
      blockDiag_apply_natAdd_castAdd]
  · refine iff_of_false ?_ (fun h => block_not_adj_castAdd_natAdd _ _ k j h.symm)
    simp [patternGraph, SimpleGraph.fromRel_adj, blockDiag_apply_castAdd_natAdd,
      blockDiag_apply_natAdd_castAdd]
  · rw [block_adj_natAdd_natAdd]
    simp [patternGraph, SimpleGraph.fromRel_adj, blockDiag_apply_natAdd_natAdd,
      Fin.natAdd_inj]



/-- Walks starting in the image of `f` stay in it and pull back along `f`, when every edge
at an image vertex ends in the image and image edges are edges of `K` (why a fill path of a
block-diagonal matrix stays inside its block: paper Remark 2.18, `rem:irred-harmless`, with
the fill paths of paper Proposition 2.10, `prop:fillpath`). -/
theorem block_walk_pullback {V W : Type*} {G : SimpleGraph W} {K : SimpleGraph V}
    (f : V → W) (hadj : ∀ a b : V, G.Adj (f a) (f b) → K.Adj a b)
    (hclosed : ∀ (a : V) (y : W), G.Adj (f a) y → ∃ b : V, y = f b)
    {x y : W} (w : G.Walk x y) (a : V) (ha : x = f a) :
    ∃ b : V, y = f b ∧ ∃ w' : K.Walk a b, ∀ z ∈ w'.support, f z ∈ w.support := by
  induction w generalizing a with
  | nil => exact ⟨a, ha, SimpleGraph.Walk.nil, by simp [ha]⟩
  | @cons u c v h p ih =>
    subst ha
    obtain ⟨c', rfl⟩ := hclosed a c h
    obtain ⟨b, hb, w', hw'⟩ := ih c' rfl
    refine ⟨b, hb, SimpleGraph.Walk.cons (hadj a c' h) w', fun z hz => ?_⟩
    rw [SimpleGraph.Walk.support_cons] at hz ⊢
    rcases List.mem_cons.mp hz with rfl | hz
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hw' z hz)



/-- Paths through a level, read inside the image of an injective `f` closed under
adjacency, are paths of `K` through the pulled-back level (paper equation (1) and
Proposition 2.10, `prop:fillpath`, for paper Remark 2.18, `rem:irred-harmless`). -/
theorem block_hasPathThrough_iff {m N : ℕ} {G : SimpleGraph (Fin N)}
    {K : SimpleGraph (Fin m)} (f : Fin m → Fin N) (hf : Function.Injective f)
    (hadj : ∀ a b : Fin m, G.Adj (f a) (f b) ↔ K.Adj a b)
    (hclosed : ∀ (a : Fin m) (y : Fin N), G.Adj (f a) y → ∃ b : Fin m, y = f b)
    (S : Finset (Fin N)) (j k : Fin m) :
    HasPathThrough G S (f j) (f k) ↔
      HasPathThrough K (Finset.univ.filter fun x => f x ∈ S) j k := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨b, hb, w', hw'⟩ :=
      block_walk_pullback f (fun a b => (hadj a b).mp) hclosed w j rfl
    obtain rfl := hf hb
    refine ⟨w', fun z hz => ?_⟩
    rcases hw _ (hw' z hz) with h | h | h
    · exact Or.inl (hf h)
    · exact Or.inr (Or.inl (hf h))
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ z, h⟩))
  · rintro ⟨w, hw⟩
    let φ : K →g G := ⟨f, fun {a b} h => (hadj a b).mpr h⟩
    refine ⟨w.map φ, fun z hz => ?_⟩
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rcases hw y hy with rfl | rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Finset.mem_filter.mp h).2)



/-- No path joins the image of `f` to a vertex outside it, when every edge at an image
vertex ends in the image (paper Remark 2.18, `rem:irred-harmless`: no fill edge crosses
the blocks). -/
theorem block_not_hasPathThrough {m N : ℕ} {G : SimpleGraph (Fin N)}
    {K : SimpleGraph (Fin m)} (f : Fin m → Fin N)
    (hadj : ∀ a b : Fin m, G.Adj (f a) (f b) → K.Adj a b)
    (hclosed : ∀ (a : Fin m) (y : Fin N), G.Adj (f a) y → ∃ b : Fin m, y = f b)
    (S : Finset (Fin N)) (j : Fin m) {y : Fin N} (hy : ∀ b : Fin m, y ≠ f b) :
    ¬ HasPathThrough G S (f j) y := by
  rintro ⟨w, -⟩
  obtain ⟨b, hb, -⟩ := block_walk_pullback f hadj hclosed w j rfl
  exact hy b hb



/-- `blockDiag_fillGraph`: the fill graph of the concatenated ordering is the disjoint
union of the blocks' fill graphs (paper Remark 2.18, `rem:irred-harmless`: "`G⁺_σ` is the
disjoint union of the blocks' fill graphs"; fill graphs as in paper Definition 2.9,
`def:fillgraph`). Proved through the fill-path theorem `fill_path` (paper
Proposition 2.10): a path of the pattern graph never leaves its block, and inside a block
the committing level of `blockOrdering σ₁ σ₂` restricts to that of `σ₁` or `σ₂`. -/
theorem blockDiag_fillGraph {n₁ n₂ : ℕ} (A₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (A₂ : Matrix (Fin n₂) (Fin n₂) ℝ) {σ₁ : List (Fin n₁)} {σ₂ : List (Fin n₂)}
    (hσ₁ : IsOrdering σ₁) (hσ₂ : IsOrdering σ₂) :
    fillGraph (blockDiag A₁ A₂) (blockOrdering σ₁ σ₂) =
      (fillGraph A₁ σ₁).map (Fin.castAddEmb n₂) ⊔ (fillGraph A₂ σ₂).map (Fin.natAddEmb n₁) := by
  have hτ := blockOrdering_isOrdering hσ₁ hσ₂
  have hpath : ∀ u v : Fin (n₁ + n₂), u ≠ v →
      ((fillGraph (blockDiag A₁ A₂) (blockOrdering σ₁ σ₂)).Adj u v ↔
        HasPathThrough ((patternGraph A₁).map (Fin.castAddEmb n₂) ⊔
          (patternGraph A₂).map (Fin.natAddEmb n₁))
          (prefixSet (blockOrdering σ₁ σ₂) u v) u v) := by
    intro u v huv
    rw [← blockDiag_patternGraph A₁ A₂]
    exact (fill_path (A := blockDiag A₁ A₂) _ hτ u v huv).1.trans
      (fill_path (A := blockDiag A₁ A₂) _ hτ u v huv).2
  have hcross : ∀ (j : Fin n₁) (k : Fin n₂),
      ¬ (fillGraph (blockDiag A₁ A₂) (blockOrdering σ₁ σ₂)).Adj
        (Fin.castAdd n₂ j) (Fin.natAdd n₁ k) := fun j k h =>
    block_not_hasPathThrough (Fin.castAdd n₂)
      (fun a b => (block_adj_castAdd_castAdd _ _ a b).mp) (block_closed_castAdd _ _) _ j
      (fun b hb => block_castAdd_ne_natAdd b k hb.symm)
      ((hpath _ _ (block_castAdd_ne_natAdd j k)).mp h)
  ext u v
  rcases block_cases u with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    rcases block_cases v with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [block_adj_castAdd_castAdd]
    by_cases hjk : j = k
    · subst hjk
      simp only [SimpleGraph.irrefl]
    · rw [hpath _ _ (fun h => hjk (Fin.castAdd_injective n₁ n₂ h)),
        block_hasPathThrough_iff (Fin.castAdd n₂) (Fin.castAdd_injective n₁ n₂)
          (block_adj_castAdd_castAdd _ _) (block_closed_castAdd _ _),
        block_filter_prefixSet_castAdd hσ₁]
      exact ((fill_path (A := A₁) σ₁ hσ₁ j k hjk).1.trans
        (fill_path (A := A₁) σ₁ hσ₁ j k hjk).2).symm
  · exact iff_of_false (hcross j k) (block_not_adj_castAdd_natAdd _ _ j k)
  · exact iff_of_false (fun h => hcross k j h.symm)
      (fun h => block_not_adj_castAdd_natAdd _ _ k j h.symm)
  · rw [block_adj_natAdd_natAdd]
    by_cases hjk : j = k
    · subst hjk
      simp only [SimpleGraph.irrefl]
    · rw [hpath _ _ (fun h => hjk (Fin.natAdd_injective n₂ n₁ h)),
        block_hasPathThrough_iff (Fin.natAdd n₁) (Fin.natAdd_injective n₂ n₁)
          (block_adj_natAdd_natAdd _ _) (block_closed_natAdd _ _),
        block_filter_prefixSet_natAdd]
      exact ((fill_path (A := A₂) σ₂ hσ₂ j k hjk).1.trans
        (fill_path (A := A₂) σ₂ hσ₂ j k hjk).2).symm



/-- Schur complements of `diag(A₁, A₂)` vanish from the first block to the second at every
level (paper Remark 2.18, `rem:irred-harmless`; Schur complements as in paper
Definition 2.2). By induction on the level through the quotient property `schur_quotient`
(paper Lemma 2.4): every pivot update has a vanishing leg. -/
theorem block_schurEntry_castAdd_natAdd {n₁ n₂ : ℕ} {A₁ : Matrix (Fin n₁) (Fin n₁) ℝ}
    {A₂ : Matrix (Fin n₂) (Fin n₂) ℝ} (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (S : Finset (Fin (n₁ + n₂))) (j : Fin n₁) (k : Fin n₂) :
    schurEntry (blockDiag A₁ A₂) S (Fin.castAdd n₂ j) (Fin.natAdd n₁ k) = 0 := by
  have hB := blockDiag_posDef hA₁ hA₂
  induction S using Finset.induction_on generalizing j k with
  | empty => rw [schurEntry_empty, blockDiag_apply_castAdd_natAdd]
  | insert v S hv ih =>
    by_cases hj : Fin.castAdd n₂ j ∈ insert v S
    · exact schurEntry_eq_zero_of_mem_left hj
    by_cases hk : Fin.natAdd n₁ k ∈ insert v S
    · rw [schurEntry_symm hB]
      exact schurEntry_eq_zero_of_mem_left hk
    rw [schur_quotient hB S v hv _ _ hj hk, pivotEntry, ih j k]
    rcases block_cases v with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [schurEntry_symm hB S (Fin.natAdd n₁ k), ih a k]
      ring
    · rw [ih j a]
      ring



/-- Schur complements of `diag(A₁, A₂)` vanish from the second block to the first at every
level (paper Remark 2.18, `rem:irred-harmless`; from `block_schurEntry_castAdd_natAdd` by
symmetry). -/
theorem block_schurEntry_natAdd_castAdd {n₁ n₂ : ℕ} {A₁ : Matrix (Fin n₁) (Fin n₁) ℝ}
    {A₂ : Matrix (Fin n₂) (Fin n₂) ℝ} (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (S : Finset (Fin (n₁ + n₂))) (k : Fin n₂) (j : Fin n₁) :
    schurEntry (blockDiag A₁ A₂) S (Fin.natAdd n₁ k) (Fin.castAdd n₂ j) = 0 := by
  rw [schurEntry_symm (blockDiag_posDef hA₁ hA₂)]
  exact block_schurEntry_castAdd_natAdd hA₁ hA₂ S j k



/-- Inside the first block, the Schur complement of `diag(A₁, A₂)` at a level `S` is the
Schur complement of `A₁` at the first-block part of `S` (paper Remark 2.18,
`rem:irred-harmless`; Schur complements as in paper Definition 2.2). By induction on the
level through the quotient property `schur_quotient` (paper Lemma 2.4): a first-block pivot
updates both sides alike, a second-block pivot has vanishing legs. -/
theorem block_schurEntry_castAdd_castAdd {n₁ n₂ : ℕ} {A₁ : Matrix (Fin n₁) (Fin n₁) ℝ}
    {A₂ : Matrix (Fin n₂) (Fin n₂) ℝ} (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (S : Finset (Fin (n₁ + n₂))) (j k : Fin n₁) (hj : Fin.castAdd n₂ j ∉ S)
    (hk : Fin.castAdd n₂ k ∉ S) :
    schurEntry (blockDiag A₁ A₂) S (Fin.castAdd n₂ j) (Fin.castAdd n₂ k) =
      schurEntry A₁ (Finset.univ.filter fun x => Fin.castAdd n₂ x ∈ S) j k := by
  have hB := blockDiag_posDef hA₁ hA₂
  induction S using Finset.induction_on generalizing j k with
  | empty =>
    have h0 : (Finset.univ.filter fun x : Fin n₁ =>
        Fin.castAdd n₂ x ∈ (∅ : Finset (Fin (n₁ + n₂)))) = ∅ := by
      simp
    rw [h0, schurEntry_empty, schurEntry_empty, blockDiag_apply_castAdd_castAdd]
  | insert v S hv ih =>
    have hjS : Fin.castAdd n₂ j ∉ S := fun h => hj (Finset.mem_insert_of_mem h)
    have hkS : Fin.castAdd n₂ k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
    rw [schur_quotient hB S v hv _ _ hj hk]
    rcases block_cases v with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · have hS : (Finset.univ.filter fun x => Fin.castAdd n₂ x ∈ insert (Fin.castAdd n₂ a) S)
          = insert a (Finset.univ.filter fun x => Fin.castAdd n₂ x ∈ S) := by
        ext x
        simp [Fin.castAdd_inj]
      have ha : a ∉ Finset.univ.filter fun x => Fin.castAdd n₂ x ∈ S := by
        simpa using hv
      have hj' : j ∉ insert a (Finset.univ.filter fun x => Fin.castAdd n₂ x ∈ S) := by
        rw [← hS]
        simpa using hj
      have hk' : k ∉ insert a (Finset.univ.filter fun x => Fin.castAdd n₂ x ∈ S) := by
        rw [← hS]
        simpa using hk
      rw [hS, schur_quotient hA₁ _ a ha j k hj' hk']
      simp only [pivotEntry, ih j k hjS hkS, ih j a hjS hv, ih k a hkS hv, ih a a hv hv]
    · have hS : (Finset.univ.filter fun x => Fin.castAdd n₂ x ∈ insert (Fin.natAdd n₁ a) S)
          = Finset.univ.filter fun x => Fin.castAdd n₂ x ∈ S := by
        ext x
        simp [block_castAdd_ne_natAdd]
      rw [hS, pivotEntry, ih j k hjS hkS, block_schurEntry_castAdd_natAdd hA₁ hA₂ S j a]
      ring



/-- Inside the second block, the Schur complement of `diag(A₁, A₂)` at a level `S` is the
Schur complement of `A₂` at the second-block part of `S` (paper Remark 2.18,
`rem:irred-harmless`; Schur complements as in paper Definition 2.2). By induction on the
level through the quotient property `schur_quotient` (paper Lemma 2.4). -/
theorem block_schurEntry_natAdd_natAdd {n₁ n₂ : ℕ} {A₁ : Matrix (Fin n₁) (Fin n₁) ℝ}
    {A₂ : Matrix (Fin n₂) (Fin n₂) ℝ} (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (S : Finset (Fin (n₁ + n₂))) (j k : Fin n₂) (hj : Fin.natAdd n₁ j ∉ S)
    (hk : Fin.natAdd n₁ k ∉ S) :
    schurEntry (blockDiag A₁ A₂) S (Fin.natAdd n₁ j) (Fin.natAdd n₁ k) =
      schurEntry A₂ (Finset.univ.filter fun x => Fin.natAdd n₁ x ∈ S) j k := by
  have hB := blockDiag_posDef hA₁ hA₂
  induction S using Finset.induction_on generalizing j k with
  | empty =>
    have h0 : (Finset.univ.filter fun x : Fin n₂ =>
        Fin.natAdd n₁ x ∈ (∅ : Finset (Fin (n₁ + n₂)))) = ∅ := by
      simp
    rw [h0, schurEntry_empty, schurEntry_empty, blockDiag_apply_natAdd_natAdd]
  | insert v S hv ih =>
    have hjS : Fin.natAdd n₁ j ∉ S := fun h => hj (Finset.mem_insert_of_mem h)
    have hkS : Fin.natAdd n₁ k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
    rw [schur_quotient hB S v hv _ _ hj hk]
    rcases block_cases v with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · have hS : (Finset.univ.filter fun x => Fin.natAdd n₁ x ∈ insert (Fin.castAdd n₂ a) S)
          = Finset.univ.filter fun x => Fin.natAdd n₁ x ∈ S := by
        ext x
        simp [block_natAdd_ne_castAdd]
      rw [hS, pivotEntry, ih j k hjS hkS, block_schurEntry_natAdd_castAdd hA₁ hA₂ S j a]
      ring
    · have hS : (Finset.univ.filter fun x => Fin.natAdd n₁ x ∈ insert (Fin.natAdd n₁ a) S)
          = insert a (Finset.univ.filter fun x => Fin.natAdd n₁ x ∈ S) := by
        ext x
        simp [Fin.natAdd_inj]
      have ha : a ∉ Finset.univ.filter fun x => Fin.natAdd n₁ x ∈ S := by
        simpa using hv
      have hj' : j ∉ insert a (Finset.univ.filter fun x => Fin.natAdd n₁ x ∈ S) := by
        rw [← hS]
        simpa using hj
      have hk' : k ∉ insert a (Finset.univ.filter fun x => Fin.natAdd n₁ x ∈ S) := by
        rw [← hS]
        simpa using hk
      rw [hS, schur_quotient hA₂ _ a ha j k hj' hk']
      simp only [pivotEntry, ih j k hjS hkS, ih j a hjS hv, ih k a hkS hv, ih a a hv hv]



/-- `blockDiag_isCleanOrdering`: clean orderings of the blocks concatenate to a clean
ordering of `diag(A₁, A₂)` (paper Remark 2.18, `rem:irred-harmless`; clean orderings as in
paper Definition 2.24, `def:clean`). A predicted-nonzero position lies inside one block
(`blockDiag_fillGraph`), where the committed Schur entry is that of the block at its own
committing level. -/
theorem blockDiag_isCleanOrdering {n₁ n₂ : ℕ} {A₁ : Matrix (Fin n₁) (Fin n₁) ℝ}
    {A₂ : Matrix (Fin n₂) (Fin n₂) ℝ} (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    {σ₁ : List (Fin n₁)} {σ₂ : List (Fin n₂)} (hσ₁ : IsOrdering σ₁) (hσ₂ : IsOrdering σ₂)
    (hc₁ : IsCleanOrdering A₁ σ₁) (hc₂ : IsCleanOrdering A₂ σ₂) :
    IsCleanOrdering (blockDiag A₁ A₂) (blockOrdering σ₁ σ₂) := by
  intro u v huv
  have huv' : ((fillGraph A₁ σ₁).map (Fin.castAddEmb n₂) ⊔
      (fillGraph A₂ σ₂).map (Fin.natAddEmb n₁)).Adj u v := by
    rw [← blockDiag_fillGraph A₁ A₂ hσ₁ hσ₂]
    exact huv
  rcases block_cases u with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    rcases block_cases v with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [block_adj_castAdd_castAdd] at huv'
    rw [block_schurEntry_castAdd_castAdd hA₁ hA₂ _ j k
        (block_left_notMem_prefixSet _ _ _) (block_right_notMem_prefixSet _ _ _),
      block_filter_prefixSet_castAdd hσ₁]
    exact hc₁ j k huv'
  · exact absurd huv' (block_not_adj_castAdd_natAdd _ _ j k)
  · exact absurd huv'.symm (block_not_adj_castAdd_natAdd _ _ k j)
  · rw [block_adj_natAdd_natAdd] at huv'
    rw [block_schurEntry_natAdd_natAdd hA₁ hA₂ _ j k
        (block_left_notMem_prefixSet _ _ _) (block_right_notMem_prefixSet _ _ _),
      block_filter_prefixSet_natAdd]
    exact hc₂ j k huv'



/-- `blockDiag_exists_clean`: if each block has a clean ordering, so does
`diag(A₁, A₂)` (paper Remark 2.18, `rem:irred-harmless`: "nothing is lost by assuming `G_A`
connected", for the literal block-diagonal form). -/
theorem blockDiag_exists_clean {n₁ n₂ : ℕ} {A₁ : Matrix (Fin n₁) (Fin n₁) ℝ}
    {A₂ : Matrix (Fin n₂) (Fin n₂) ℝ} (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (h₁ : ∃ σ₁ : List (Fin n₁), IsOrdering σ₁ ∧ IsCleanOrdering A₁ σ₁)
    (h₂ : ∃ σ₂ : List (Fin n₂), IsOrdering σ₂ ∧ IsCleanOrdering A₂ σ₂) :
    ∃ σ : List (Fin (n₁ + n₂)), IsOrdering σ ∧ IsCleanOrdering (blockDiag A₁ A₂) σ := by
  obtain ⟨σ₁, hσ₁, hc₁⟩ := h₁
  obtain ⟨σ₂, hσ₂, hc₂⟩ := h₂
  exact ⟨blockOrdering σ₁ σ₂, blockOrdering_isOrdering hσ₁ hσ₂,
    blockDiag_isCleanOrdering hA₁ hA₂ hσ₁ hσ₂ hc₁ hc₂⟩

end CholeskyCancellations

/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Section_2_SettingVocabularyAndConjectures.A_SchurComplement

/-! # Pattern graphs (paper Section 2)

Pattern, elimination-step, game, and fill graphs; orderings and committing prefixes; walks and fill paths; the numeric-vs-symbolic comparison. Split from `Defs.lean`.
-/

open scoped Matrix

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): vertices `Fin n`, SPD = `Matrix.PosDef`, levels `Finset (Fin n)`, pivot-order list orderings, Schur entries through `schurEntry` only. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}


/-- `patternGraph A`: the pattern graph `G_A`, adjacent iff distinct
and joined by a nonzero entry (paper Definition 2.7, `def:fill`).
Built with `SimpleGraph.fromRel`, which symmetrizes; for symmetric
(SPD) matrices this is exactly the paper's graph. -/
def patternGraph (A : Matrix (Fin n) (Fin n) ℝ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => A i j ≠ 0



/-- `elimStep G v`: one step of the elimination game on the full vertex
set — complete the neighborhood of `v` into a clique (paper
Definition 2.7, `def:fill`). The paper then restricts to survivors;
adjacency between survivors is unaffected by that restriction. -/
def elimStep (G : SimpleGraph (Fin n)) (v : Fin n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x y => G.Adj x y ∨ (G.Adj x v ∧ G.Adj y v)



/-- `gameGraph G l`: the cumulative game graph after eliminating the
vertices of `l` in list order (paper Definitions 2.7 and 2.9). For a
full ordering `σ` this is the fill graph `G⁺_σ`; for `l` enumerating a
level `S`, its adjacency between survivors is the paper's `G_S`. -/
def gameGraph (G : SimpleGraph (Fin n)) (l : List (Fin n)) : SimpleGraph (Fin n) :=
  l.foldl elimStep G



/-- `Enumerates l S`: the list `l` enumerates the level `S` exactly
once (used wherever the paper's set-indexed `G_S` is read off one of
its orderings). -/
def Enumerates (l : List (Fin n)) (S : Finset (Fin n)) : Prop :=
  l.Nodup ∧ l.toFinset = S



/-- `IsOrdering σ`: `σ` lists every vertex exactly once, in pivot
order (paper Section 2 usage of an ordering `σ = (v₁, …, vₙ)`). -/
def IsOrdering (σ : List (Fin n)) : Prop :=
  σ.Nodup ∧ σ.length = n



/-- `prefixList σ j k`: the vertices preceding both `j` and `k` in `σ`,
in order (paper Proposition 2.10's set `S`, as its ordering in `σ`). -/
def prefixList (σ : List (Fin n)) (j k : Fin n) : List (Fin n) :=
  σ.takeWhile fun x => x ≠ j ∧ x ≠ k



/-- `prefixSet σ j k`: the predecessors of the earlier of `j, k` in `σ`
(paper Definitions 2.23 and 2.24). -/
def prefixSet (σ : List (Fin n)) (j k : Fin n) : Finset (Fin n) :=
  (prefixList σ j k).toFinset



/-- Pointwise-equal predicates give equal `takeWhile`s. -/
theorem takeWhile_ext (l : List (Fin n)) (p q : Fin n → Bool)
    (hpq : ∀ x, p x = q x) : l.takeWhile p = l.takeWhile q := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.takeWhile_cons, hpq x, ih]



/-- The committing prefix of a pair does not depend on the pair's
order. -/
theorem prefixSet_comm (σ : List (Fin n)) (j k : Fin n) :
    prefixSet σ k j = prefixSet σ j k := by
  have htw : σ.takeWhile (fun x => decide (x ≠ k ∧ x ≠ j))
      = σ.takeWhile (fun x => decide (x ≠ j ∧ x ≠ k)) :=
    takeWhile_ext σ _ _ (fun x => by
      by_cases h1 : x = k <;> by_cases h2 : x = j <;> simp [h1, h2])
  simp only [prefixSet, prefixList]
  rw [htw]



/-- The committing prefix list of a pair does not depend on the
pair's order. -/
theorem prefixList_comm (σ : List (Fin n)) (j k : Fin n) :
    prefixList σ k j = prefixList σ j k :=
  takeWhile_ext σ _ _ (fun x => by
    by_cases h1 : x = k <;> by_cases h2 : x = j <;> simp [h1, h2])



/-- `fillGraph A σ`: the fill graph `G⁺_σ` of an ordering (paper
Definition 2.9, `def:fillgraph`). Bridge: the paper's game deletes
each pivot, so no fill edge incident to `j` is ever created after
`j` is pivoted, and membership of `{j, k}` is decided at the
committing prefix (the paper's proof of Proposition 2.10, (1)↔(2)).
Our `gameGraph` keeps eliminated vertices — adjacency between
survivors agrees with the paper's `G_S` — so the cumulative fill
graph is read off at the committing prefix of each pair; that this
agrees with the paper's cumulative definition is proved below as
`fillGraphGame_eq_fillGraph` (the (1)↔(2) part of
Proposition 2.10). (Reading
it off the full list instead would add spurious edges: on the path
`0-1-2` with `σ = [0, 1, 2]` the undeleted game creates `{0, 2}` at
the second step, after `0` has been pivoted.) -/
def fillGraph (A : Matrix (Fin n) (Fin n) ℝ) (σ : List (Fin n)) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun j k =>
    (gameGraph (patternGraph A) (prefixList σ j k)).Adj j k



/-- Fill-graph adjacency is level-graph adjacency at the committing
prefix (by the definition above and `prefixList_comm`). -/
theorem fillGraph_adj_iff (σ : List (Fin n)) (j k : Fin n) :
    (fillGraph A σ).Adj j k ↔
      (gameGraph (patternGraph A) (prefixList σ j k)).Adj j k := by
  constructor
  · intro h
    have hadj : j ≠ k ∧
        ((gameGraph (patternGraph A) (prefixList σ j k)).Adj j k ∨
          (gameGraph (patternGraph A) (prefixList σ k j)).Adj k j) := by
      simpa [fillGraph, SimpleGraph.fromRel_adj] using h
    rcases hadj.2 with h' | h'
    · exact h'
    · rw [prefixList_comm] at h'
      exact h'.symm
  · intro h
    simp [fillGraph, SimpleGraph.fromRel_adj, h.ne, h]



/-- `HasPathThrough G S j k`: `G` has a `j`–`k` walk all of whose
interior vertices lie in `S` (paper equation (1) and
Proposition 2.10 (3)). -/
def HasPathThrough (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (j k : Fin n) : Prop :=
  ∃ w : G.Walk j k, ∀ x ∈ w.support, x = j ∨ x = k ∨ x ∈ S



/-- `numericPattern A S`: the numeric pattern `P_S` of `A/A_S` (paper
Definition 2.12, `def:numeric`), on the full vertex set; the junk
zeros of `schurEntry` keep it supported on the survivors. -/
noncomputable def numericPattern (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun j k => schurEntry A S j k ≠ 0



/-- `factorPattern A σ`: the factor pattern `Gᴸ_σ`, defined through
committed entries (paper Definitions 2.12 and 2.23): `{j, k}` is
adjacent iff its value at the committing prefix level is nonzero.
Bridge: the paper defines this from the Cholesky factor `L`; here
that factor is assembled as `factorMatrix` from the factor entries of
Definition 2.23, proved to satisfy `L Lᵀ = A`
(`factorMatrix_mul_transpose`), to be lower triangular in
`σ`-order (`factorMatrix_eq_zero_of_afterIn`) with positive
diagonal (`factorMatrix_diag`), and this graph is its pattern
(`factorPattern_adj_iff_factorEntry`). -/
noncomputable def factorPattern (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : List (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun j k => schurEntry A (prefixSet σ j k) j k ≠ 0



/-- `predictedNonzero A σ j k`: `{j, k}` is a predicted-nonzero
position for `σ` (paper Definition 2.12, `def:numeric`). -/
def PredictedNonzero (A : Matrix (Fin n) (Fin n) ℝ) (σ : List (Fin n))
    (j k : Fin n) : Prop :=
  (fillGraph A σ).Adj j k



/-- Adjacency in the numeric pattern is a nonzero Schur entry
(the relation is symmetric by `schurEntry_symm`). -/
theorem numericPattern_adj (hA : A.PosDef) (S : Finset (Fin n))
    (j k : Fin n) (h : (numericPattern A S).Adj j k) :
    j ≠ k ∧ schurEntry A S j k ≠ 0 := by
  have hadj : j ≠ k ∧ (schurEntry A S j k ≠ 0 ∨ schurEntry A S k j ≠ 0) := by
    simpa [numericPattern, SimpleGraph.fromRel_adj] using h
  refine ⟨hadj.1, ?_⟩
  rcases hadj.2 with h' | h'
  · exact h'
  · rwa [schurEntry_symm hA] at h'



/-- A nonzero Schur entry between distinct vertices is adjacency in
the numeric pattern. -/
theorem numericPattern_adj_mk (S : Finset (Fin n)) (j k : Fin n)
    (hjk : j ≠ k) (h : schurEntry A S j k ≠ 0) :
    (numericPattern A S).Adj j k := by
  simp [numericPattern, SimpleGraph.fromRel_adj, hjk, h]



/-- One elimination step only adds edges. -/
theorem elimStep_adj_of_adj (G : SimpleGraph (Fin n)) (v j k : Fin n)
    (h : G.Adj j k) : (elimStep G v).Adj j k := by
  simp [elimStep, SimpleGraph.fromRel_adj, h.ne, h, h.symm]



/-- One elimination step completes the pivot's neighborhood. -/
theorem elimStep_adj_of_legs (G : SimpleGraph (Fin n)) (v j k : Fin n)
    (hjk : j ≠ k) (hjv : G.Adj j v) (hkv : G.Adj k v) :
    (elimStep G v).Adj j k := by
  simp [elimStep, SimpleGraph.fromRel_adj, hjk, hjv, hkv]



/-- Fill from a path (paper Example 2.13, `ex:fill-path`): for an
SPD matrix with the path pattern `0-1-2` on `Fin 3`, pivoting `1`
first creates the fill edge `{0,2}` in the level graph and the fill
graph, and the created entry `-A₀₁A₁₂/A₁₁` is nonzero. -/
theorem fill_path_example {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A.PosDef) (h01 : (patternGraph A).Adj 0 1)
    (h12 : (patternGraph A).Adj 1 2)
    (h02 : ¬ (patternGraph A).Adj 0 2) :
    (gameGraph (patternGraph A) [1]).Adj 0 2 ∧
    (fillGraph A [1, 0, 2]).Adj 0 2 ∧
    schurEntry A {1} 0 2 = -A 0 1 * A 1 2 / A 1 1 ∧
    schurEntry A {1} 0 2 ≠ 0 := by
  classical
  have hgame : (gameGraph (patternGraph A) [1]).Adj 0 2 := by
    have h : gameGraph (patternGraph A) [(1 : Fin 3)]
        = elimStep (patternGraph A) 1 := rfl
    rw [h]
    exact elimStep_adj_of_legs _ _ _ _ (by decide) h01 h12.symm
  have hfill : (fillGraph A [1, 0, 2]).Adj 0 2 := by
    rw [fillGraph_adj_iff]
    have hpre : prefixList [(1 : Fin 3), 0, 2] 0 2 = [1] := by
      simp [prefixList]
    rw [hpre]
    exact hgame
  have hA02 : A 0 2 = 0 := by
    by_contra h
    exact h02 (by
      simp [patternGraph, SimpleGraph.fromRel_adj,
        show (0 : Fin 3) ≠ 2 by decide, h])
  have hentry : ∀ {i j : Fin 3}, (patternGraph A).Adj i j →
      A i j ≠ 0 := by
    intro i j hij
    have h2 : i ≠ j ∧ (A i j ≠ 0 ∨ A j i ≠ 0) := by
      simpa [patternGraph, SimpleGraph.fromRel_adj] using hij
    rcases h2.2 with h | h
    · exact h
    · rwa [posDef_apply_comm hA] at h
  have hval : schurEntry A {1} 0 2 = -A 0 1 * A 1 2 / A 1 1 := by
    have h1 : ({1} : Finset (Fin 3)) = insert 1 ∅ := rfl
    rw [h1, schur_quotient hA ∅ 1 (by simp) 0 2 (by decide)
      (by decide)]
    unfold pivotEntry
    rw [schurEntry_empty, schurEntry_empty, schurEntry_empty,
      schurEntry_empty, hA02, posDef_apply_comm hA 2 1]
    ring
  refine ⟨hgame, hfill, hval, ?_⟩
  rw [hval]
  have hpos : 0 < schurEntry A ∅ (1 : Fin 3) 1 :=
    schurEntry_pos hA ∅ (by simp)
  rw [schurEntry_empty] at hpos
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (hentry h01))
    (hentry h12)) (ne_of_gt hpos)



/-- Game-graph adjacency persists under further eliminations. -/
theorem gameGraph_adj_mono_append (G : SimpleGraph (Fin n))
    (l₁ l₂ : List (Fin n)) (j k : Fin n)
    (h : (gameGraph G l₁).Adj j k) :
    (gameGraph G (l₁ ++ l₂)).Adj j k := by
  have key : ∀ (l : List (Fin n)) (G : SimpleGraph (Fin n)),
      G.Adj j k → (l.foldl elimStep G).Adj j k := by
    intro l
    induction l with
    | nil => intro G hG; simpa using hG
    | cons v l ih =>
      intro G hG
      exact ih (elimStep G v) (elimStep_adj_of_adj G v j k hG)
  rw [gameGraph, List.foldl_append]
  exact key l₂ _ h



/-- The numeric pattern at a level is contained in the level graph:
a nonzero Schur entry is game-adjacent (the first display in paper
Definition 2.12, `def:numeric`). Proved by snoc induction on the
elimination list: the quotient rule writes the new entry from the
old entry and the two legs, matching one elimination-game step. -/
theorem numeric_le_gameGraph (hA : A.PosDef) (l : List (Fin n))
    (j k : Fin n) (h : (numericPattern A l.toFinset).Adj j k) :
    (gameGraph (patternGraph A) l).Adj j k := by
  induction l using List.reverseRecOn generalizing j k with
  | nil =>
    obtain ⟨hjk, hne⟩ := numericPattern_adj hA _ j k h
    have hnil : ([].toFinset : Finset (Fin n)) = ∅ := by simp
    rw [hnil, schurEntry_empty] at hne
    simp [gameGraph, patternGraph, SimpleGraph.fromRel_adj, hjk, hne]
  | append_singleton l v ih =>
    have hS : (l ++ [v]).toFinset = insert v l.toFinset := by
      ext x
      simp
    have hG : gameGraph (patternGraph A) (l ++ [v])
        = elimStep (gameGraph (patternGraph A) l) v := by
      simp [gameGraph, List.foldl_append]
    rw [hS] at h
    obtain ⟨hjk, hne⟩ := numericPattern_adj hA _ j k h
    rw [hG]
    by_cases hvS : v ∈ l.toFinset
    · rw [Finset.insert_eq_of_mem hvS] at hne
      exact elimStep_adj_of_adj _ v j k
        (ih j k (numericPattern_adj_mk _ j k hjk hne))
    · have hj : j ∉ insert v l.toFinset := by
        intro hj
        apply hne
        unfold schurEntry
        split
        · rename_i hc
          exact absurd hj (Finset.mem_compl.mp hc)
        · rfl
      have hk : k ∉ insert v l.toFinset := by
        intro hk
        apply hne
        unfold schurEntry
        split
        · split
          · rename_i _ hc
            exact absurd hk (Finset.mem_compl.mp hc)
          · rfl
        · rfl
      rw [schur_quotient hA l.toFinset v hvS j k hj hk] at hne
      unfold pivotEntry at hne
      by_cases hMjk : schurEntry A l.toFinset j k = 0
      · rw [hMjk] at hne
        simp only [zero_sub, neg_ne_zero, div_ne_zero_iff,
          mul_ne_zero_iff] at hne
        obtain ⟨⟨hjv, hkv⟩, -⟩ := hne
        have hjne : j ≠ v :=
          fun h => hj (by rw [h]; exact Finset.mem_insert_self v _)
        have hkne : k ≠ v :=
          fun h => hk (by rw [h]; exact Finset.mem_insert_self v _)
        exact elimStep_adj_of_legs _ v j k hjk
          (ih j v (numericPattern_adj_mk _ j v hjne hjv))
          (ih k v (numericPattern_adj_mk _ k v hkne hkv))
      · exact elimStep_adj_of_adj _ v j k
          (ih j k (numericPattern_adj_mk _ j k hjk hMjk))



/-- `numeric_le_symbolic`: the numeric pattern is contained in the
symbolic one at every level and for the factor (the display in paper
Definition 2.12, `def:numeric`). Proved: the level statement is
`numeric_le_gameGraph`; the factor statement is the same lemma at
the committing prefix, which is how `fillGraph` is read off. -/
theorem numeric_le_symbolic (hA : A.PosDef) :
    (∀ (l : List (Fin n)) (j k : Fin n),
      (numericPattern A l.toFinset).Adj j k →
        (gameGraph (patternGraph A) l).Adj j k) ∧
    ∀ σ : List (Fin n), IsOrdering σ →
      ∀ j k : Fin n, (factorPattern A σ).Adj j k →
        PredictedNonzero A σ j k := by
  refine ⟨fun l j k h => numeric_le_gameGraph hA l j k h, ?_⟩
  intro σ _hσ j k h
  have hadj : j ≠ k ∧ (schurEntry A (prefixSet σ j k) j k ≠ 0
      ∨ schurEntry A (prefixSet σ k j) k j ≠ 0) := by
    simpa [factorPattern, SimpleGraph.fromRel_adj] using h
  have hne : schurEntry A (prefixSet σ j k) j k ≠ 0 := by
    rcases hadj.2 with h' | h'
    · exact h'
    · rw [prefixSet_comm, schurEntry_symm hA] at h'
      exact h'
  have hpre := numeric_le_gameGraph hA (prefixList σ j k) j k
    (numericPattern_adj_mk _ j k hadj.1 hne)
  change (fillGraph A σ).Adj j k
  rwa [fillGraph_adj_iff]




/-- Extraction: adjacency in an elimination step. -/
theorem elimStep_adj_cases {G : SimpleGraph (Fin n)} (v j k : Fin n) (h : (elimStep G v).Adj j k) :
    G.Adj j k ∨ (G.Adj j v ∧ G.Adj k v) := by
  have hadj : j ≠ k ∧
      ((G.Adj j k ∨ (G.Adj j v ∧ G.Adj k v)) ∨
        (G.Adj k j ∨ (G.Adj k v ∧ G.Adj j v))) := by
    simpa [elimStep, SimpleGraph.fromRel_adj] using h
  rcases hadj.2 with (h | h) | (h | h)
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h.symm
  · exact Or.inr ⟨h.2, h.1⟩



/-- Walks in an elimination-step graph lift to walks in the original
graph, visiting only the pivot extra. -/
theorem walk_lift {G : SimpleGraph (Fin n)} (v : Fin n) :
    ∀ {a b : Fin n} (w : (elimStep G v).Walk a b),
    ∃ w' : G.Walk a b, ∀ x ∈ w'.support, x ∈ w.support ∨ x = v := by
  intro a b w
  induction w with
  | nil => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | cons h p ih =>
    obtain ⟨w', hw'⟩ := ih
    rcases elimStep_adj_cases v _ _ h with h1 | ⟨h1, h2⟩
    · refine ⟨SimpleGraph.Walk.cons h1 w', ?_⟩
      intro x hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      rcases hx with rfl | hx
      · exact Or.inl (Or.inl rfl)
      · rcases hw' x hx with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
    · refine ⟨SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2.symm w'), ?_⟩
      intro x hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      rcases hx with rfl | rfl | hx
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr rfl
      · rcases hw' x hx with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'



/-- Surgery: a walk avoiding the pivot at its ends, with support in
`T`, becomes a walk in the elimination-step graph with support in
`T \ {v}` (each interior visit to `v` is shortcut through the new
clique edges). By induction on a length bound. -/
theorem walk_surgery {G : SimpleGraph (Fin n)} (v : Fin n) (T : Finset (Fin n)) :
    ∀ (m : ℕ) {a b : Fin n} (w : G.Walk a b), w.length ≤ m →
      (∀ x ∈ w.support, x ∈ T) → a ≠ v → b ≠ v → a ≠ b →
        ∃ w' : (elimStep G v).Walk a b, ∀ x ∈ w'.support, x ∈ T.erase v := by
  intro m
  induction m with
  | zero =>
    intro a b w hlen _hs _hav _hbv hab
    cases w with
    | nil => exact absurd rfl hab
    | cons h p => simp [SimpleGraph.Walk.length_cons] at hlen
  | succ m ih =>
    intro a b w hlen hs hav hbv hab
    cases w with
    | nil => exact absurd rfl hab
    | cons h p =>
      rename_i c
      rw [SimpleGraph.Walk.length_cons] at hlen
      have hplen : p.length ≤ m := by omega
      have hsub : ∀ x ∈ p.support, x ∈ (SimpleGraph.Walk.cons h p).support := by
        intro x hx
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ hx
      have haT : a ∈ T.erase v := by
        rw [Finset.mem_erase]
        refine ⟨hav, hs a ?_⟩
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_self
      have hbT : b ∈ T.erase v := by
        rw [Finset.mem_erase]
        exact ⟨hbv, hs b (SimpleGraph.Walk.end_mem_support _)⟩
      have hedge : ∀ (hadj : (elimStep G v).Adj a b),
          ∃ w' : (elimStep G v).Walk a b,
            ∀ x ∈ w'.support, x ∈ T.erase v := by
        intro hadj
        refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
        intro x hx
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · exact haT
        · exact hbT
        · exact (List.not_mem_nil hx).elim
      by_cases hcb : c = b
      · subst hcb
        exact hedge (elimStep_adj_of_adj G v a c h)
      · by_cases hca : c = a
        · subst hca
          exact ih p hplen (fun x hx => hs x (hsub x hx)) hav hbv hab
        · by_cases hcv : c = v
          · subst hcv
            cases p with
            | nil => exact absurd rfl hbv
            | cons h₂ p₂ =>
              rename_i d
              rw [SimpleGraph.Walk.length_cons] at hplen
              have hp2len : p₂.length ≤ m := by omega
              have hsub2 : ∀ x ∈ p₂.support, x ∈ T := by
                intro x hx
                apply hs
                rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
              by_cases hdb : d = b
              · subst hdb
                exact hedge (elimStep_adj_of_legs G c a d hab h h₂.symm)
              · by_cases hda : d = a
                · subst hda
                  exact ih p₂ hp2len hsub2 hav hbv hab
                · have hdv : d ≠ c := fun hdv => h₂.ne hdv.symm
                  obtain ⟨w₂, hw₂⟩ := ih p₂ hp2len hsub2 hdv hbv hdb
                  refine ⟨SimpleGraph.Walk.cons
                    (elimStep_adj_of_legs G c a d (fun h' => hda h'.symm)
                      h h₂.symm) w₂, ?_⟩
                  intro x hx
                  simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
                  rcases hx with rfl | hx
                  · exact haT
                  · exact hw₂ x hx
          · obtain ⟨w₁, hw₁⟩ := ih p hplen (fun x hx => hs x (hsub x hx))
              hcv hbv hcb
            refine ⟨SimpleGraph.Walk.cons (elimStep_adj_of_adj G v a c h) w₁, ?_⟩
            intro x hx
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact haT
            · exact hw₁ x hx



/-- The path characterization of game-graph adjacency (equation (1)
of the paper): for survivors `j k`, adjacency after eliminating `l`
is a `j`–`k` walk through the eliminated set. -/
theorem gameGraph_adj_iff_path : ∀ (H : SimpleGraph (Fin n))
    (l : List (Fin n)) (S : Finset (Fin n)), Enumerates l S →
    ∀ j k : Fin n, j ∉ S → k ∉ S → j ≠ k →
      ((gameGraph H l).Adj j k ↔ HasPathThrough H S j k) := by
  intro H l
  induction l generalizing H with
  | nil =>
    intro S henum j k _hj _hk hjk
    have hS : S = ∅ := by
      have h2 := henum.2
      simp at h2
      exact h2.symm
    subst hS
    constructor
    · intro h
      have h' : H.Adj j k := h
      refine ⟨SimpleGraph.Walk.cons h' SimpleGraph.Walk.nil, ?_⟩
      intro x hx
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl rfl
      · rw [List.mem_singleton] at hx
        exact Or.inr (Or.inl hx)
    · intro hpath
      obtain ⟨w, hw⟩ := hpath
      cases w with
      | nil => exact absurd rfl hjk
      | cons h p =>
        rename_i c
        have hcmem : c ∈ (SimpleGraph.Walk.cons h p).support := by
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ p.start_mem_support
        have hc := hw c hcmem
        rcases hc with hc | hc | hc
        · exact absurd hc.symm h.ne
        · subst hc
          exact h
        · exact absurd hc (Finset.notMem_empty c)
  | cons v l' ih =>
    intro S henum j k hj hk hjk
    obtain ⟨hvnot, hnd'⟩ := List.nodup_cons.mp henum.1
    have hSeq : S = insert v l'.toFinset := by
      rw [← henum.2, List.toFinset_cons]
    have henum' : Enumerates l' l'.toFinset := ⟨hnd', rfl⟩
    have hj' : j ∉ insert v l'.toFinset := hSeq ▸ hj
    have hk' : k ∉ insert v l'.toFinset := hSeq ▸ hk
    have hjS' : j ∉ l'.toFinset :=
      fun h => hj' (Finset.mem_insert_of_mem h)
    have hkS' : k ∉ l'.toFinset :=
      fun h => hk' (Finset.mem_insert_of_mem h)
    have hjv : j ≠ v :=
      fun h => hj' (Finset.mem_insert.mpr (Or.inl h))
    have hkv : k ≠ v :=
      fun h => hk' (Finset.mem_insert.mpr (Or.inl h))
    have hgame : gameGraph H (v :: l') = gameGraph (elimStep H v) l' := rfl
    rw [hgame]
    constructor
    · intro hg
      obtain ⟨w, hw⟩ :=
        (ih (elimStep H v) _ henum' j k hjS' hkS' hjk).mp hg
      obtain ⟨w', hw'⟩ := walk_lift (G := H) v w
      refine ⟨w', fun x hx => ?_⟩
      rcases hw' x hx with hxw | hxeq
      · rcases hw x hxw with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (hSeq.symm ▸ Finset.mem_insert_of_mem h'))
      · exact Or.inr (Or.inr
          (hxeq.symm ▸ hSeq.symm ▸ Finset.mem_insert_self v _))
    · intro hpath
      obtain ⟨w, hw⟩ := hpath
      have hs : ∀ x ∈ w.support, x ∈ insert j (insert k S) := by
        intro x hx
        rcases hw x hx with hxj | hxk | hxS
        · exact Finset.mem_insert.mpr (Or.inl hxj)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hxk))
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxS)
      obtain ⟨w', hw'⟩ := walk_surgery (G := H) v (insert j (insert k S))
        w.length w le_rfl hs hjv hkv hjk
      have hpath' : HasPathThrough (elimStep H v) l'.toFinset j k := by
        refine ⟨w', fun x hx => ?_⟩
        obtain ⟨hxv, hxT⟩ := Finset.mem_erase.mp (hw' x hx)
        rcases Finset.mem_insert.mp hxT with rfl | hxT
        · exact Or.inl rfl
        · rcases Finset.mem_insert.mp hxT with rfl | hxS
          · exact Or.inr (Or.inl rfl)
          · rcases Finset.mem_insert.mp (hSeq ▸ hxS) with hxvv | hxS'
            · exact absurd hxvv hxv
            · exact Or.inr (Or.inr hxS')
      exact (ih (elimStep H v) _ henum' j k hjS' hkS' hjk).mpr hpath'



/-- `takeWhile` over an append whose left part satisfies the
predicate everywhere. -/
theorem takeWhile_append_of_forall {p : Fin n → Bool}
    {l₀ : List (Fin n)} (hall : ∀ x ∈ l₀, p x = true)
    (t : List (Fin n)) :
    (l₀ ++ t).takeWhile p = l₀ ++ t.takeWhile p := by
  induction l₀ with
  | nil => rfl
  | cons y l₀ ih =>
      rw [List.cons_append, List.takeWhile_cons_of_pos
        (hall y (List.mem_cons_self)), List.cons_append,
        ih (fun x hx => hall x (List.mem_cons_of_mem y hx))]



/-- Members of a committing prefix precede both endpoints. -/
theorem mem_prefixList_imp {σ : List (Fin n)} {j k x : Fin n}
    (h : x ∈ prefixList σ j k) : x ≠ j ∧ x ≠ k := by
  have h2 : ∀ l : List (Fin n),
      ∀ y ∈ l.takeWhile (fun x => decide (x ≠ j ∧ x ≠ k)),
        y ≠ j ∧ y ≠ k := by
    intro l
    induction l with
    | nil => intro y hy; simp at hy
    | cons a l ih =>
        intro y hy
        rw [List.takeWhile_cons] at hy
        split_ifs at hy with ha
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact of_decide_eq_true ha
          · exact ih y hy
        · simp at hy
  exact h2 σ x h



/-- An edge of a level graph between two survivors is either an
original edge or was created at some step of the elimination. -/
theorem gameGraph_adj_cases_created {G : SimpleGraph (Fin n)} :
    ∀ (l : List (Fin n)) (j k : Fin n), j ∉ l → k ∉ l → j ≠ k →
      (gameGraph G l).Adj j k →
      G.Adj j k ∨ ∃ (l₁ : List (Fin n)) (v : Fin n)
        (l₂ : List (Fin n)), l = l₁ ++ v :: l₂ ∧
          (gameGraph G l₁).Adj j v ∧ (gameGraph G l₁).Adj k v := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
      intro j k _ _ _ h
      exact Or.inl h
  | append_singleton l v ih =>
      intro j k hj hk hjk h
      have hG : gameGraph G (l ++ [v])
          = elimStep (gameGraph G l) v := by
        simp [gameGraph, List.foldl_append]
      rw [hG] at h
      rcases elimStep_adj_cases v j k h with h | ⟨hjv, hkv⟩
      · have hj' : j ∉ l := fun hjl => hj (List.mem_append_left [v] hjl)
        have hk' : k ∉ l := fun hkl => hk (List.mem_append_left [v] hkl)
        rcases ih j k hj' hk' hjk h with h | ⟨l₁, v', l₂, hl, h1, h2⟩
        · exact Or.inl h
        · refine Or.inr ⟨l₁, v', l₂ ++ [v], ?_, h1, h2⟩
          rw [hl, List.append_assoc]
          rfl
      · exact Or.inr ⟨l, v, [], by simp, hjv, hkv⟩



/-- `fillGraphGame A σ`: the paper's cumulative fill graph
`G^+_σ` (paper Definition 2.9, `def:fillgraph`): original edges of
`G_A` together with every fill edge created at any step of the
elimination game along `σ` — a pair of survivors joined when their
common neighbour is pivoted. (The extra requirement in the paper
that a created edge be absent before its step does not change the
cumulative union.) -/
def fillGraphGame (A : Matrix (Fin n) (Fin n) ℝ) (σ : List (Fin n)) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun j k =>
    (patternGraph A).Adj j k ∨
    ∃ (l : List (Fin n)) (v : Fin n) (t : List (Fin n)),
      σ = l ++ v :: t ∧ j ∉ l ∧ k ∉ l ∧ j ≠ v ∧ k ≠ v ∧
      (gameGraph (patternGraph A) l).Adj j v ∧
      (gameGraph (patternGraph A) l).Adj k v



/-- Adjacency in the cumulative fill graph, unfolded. -/
theorem fillGraphGame_adj_iff {A : Matrix (Fin n) (Fin n) ℝ}
    {σ : List (Fin n)} {j k : Fin n} (hjk : j ≠ k) :
    (fillGraphGame A σ).Adj j k ↔
      (patternGraph A).Adj j k ∨
      ∃ (l : List (Fin n)) (v : Fin n) (t : List (Fin n)),
        σ = l ++ v :: t ∧ j ∉ l ∧ k ∉ l ∧ j ≠ v ∧ k ≠ v ∧
        (gameGraph (patternGraph A) l).Adj j v ∧
        (gameGraph (patternGraph A) l).Adj k v := by
  have hadj : (fillGraphGame A σ).Adj j k ↔
      j ≠ k ∧ (((patternGraph A).Adj j k ∨
        ∃ (l : List (Fin n)) (v : Fin n) (t : List (Fin n)),
          σ = l ++ v :: t ∧ j ∉ l ∧ k ∉ l ∧ j ≠ v ∧ k ≠ v ∧
          (gameGraph (patternGraph A) l).Adj j v ∧
          (gameGraph (patternGraph A) l).Adj k v) ∨
        ((patternGraph A).Adj k j ∨
        ∃ (l : List (Fin n)) (v : Fin n) (t : List (Fin n)),
          σ = l ++ v :: t ∧ k ∉ l ∧ j ∉ l ∧ k ≠ v ∧ j ≠ v ∧
          (gameGraph (patternGraph A) l).Adj k v ∧
          (gameGraph (patternGraph A) l).Adj j v)) := by
    simp [fillGraphGame, SimpleGraph.fromRel_adj]
  rw [hadj]
  constructor
  · rintro ⟨-, (h | ⟨l, v, t, hs, hj, hk, hjv, hkv, h1, h2⟩) |
      (h | ⟨l, v, t, hs, hk, hj, hkv, hjv, h1, h2⟩)⟩
    · exact Or.inl h
    · exact Or.inr ⟨l, v, t, hs, hj, hk, hjv, hkv, h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨l, v, t, hs, hj, hk, hjv, hkv, h2, h1⟩
  · rintro (h | ⟨l, v, t, hs, hj, hk, hjv, hkv, h1, h2⟩)
    · exact ⟨hjk, Or.inl (Or.inl h)⟩
    · exact ⟨hjk, Or.inl (Or.inr ⟨l, v, t, hs, hj, hk, hjv, hkv, h1, h2⟩)⟩



/-- The cumulative fill graph of the paper's Definition 2.9 is
the committing-prefix graph `fillGraph`: this is the (1)⇔(2) part
of paper Proposition 2.10, `prop:fillpath` (the (2)⇔(3) path
characterization is `fill_path`). -/
theorem fillGraphGame_eq_fillGraph (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : List (Fin n)) (hσ : IsOrdering σ) :
    fillGraphGame A σ = fillGraph A σ := by
  ext j k
  by_cases hjk : j = k
  · subst hjk
    constructor <;> intro h
    · exact (h.ne rfl).elim
    · exact (h.ne rfl).elim
  rw [fillGraphGame_adj_iff hjk, fillGraph_adj_iff]
  have hσmem : ∀ x : Fin n, x ∈ σ := by
    intro x
    have h1 : σ.toFinset = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [List.toFinset_card_of_nodup hσ.1, hσ.2, Fintype.card_fin]
    exact List.mem_toFinset.mp (by rw [h1]; exact Finset.mem_univ x)
  constructor
  · rintro (h | ⟨l, v, t, hσeq, hjl, hkl, hjv, hkv, hlegj, hlegk⟩)
    · have h0 : (gameGraph (patternGraph A)
          ([] : List (Fin n))).Adj j k := h
      have h2 := gameGraph_adj_mono_append (patternGraph A) []
        (prefixList σ j k) j k h0
      simpa using h2
    · have hstep : (gameGraph (patternGraph A) (l ++ [v])).Adj
          j k := by
        have hG : gameGraph (patternGraph A) (l ++ [v])
            = elimStep (gameGraph (patternGraph A) l) v := by
          simp [gameGraph, List.foldl_append]
        rw [hG]
        exact elimStep_adj_of_legs _ _ _ _ hjk hlegj hlegk
      have hpre : prefixList σ j k
          = (l ++ [v]) ++ t.takeWhile
            (fun x => decide (x ≠ j ∧ x ≠ k)) := by
        rw [prefixList, hσeq,
          show l ++ v :: t = (l ++ [v]) ++ t by
            rw [List.append_assoc]; rfl]
        apply takeWhile_append_of_forall
        intro x hx
        rw [decide_eq_true_eq]
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact ⟨fun h => hjl (h ▸ hx), fun h => hkl (h ▸ hx)⟩
        · exact ⟨Ne.symm hjv, Ne.symm hkv⟩
      rw [hpre]
      exact gameGraph_adj_mono_append _ _ _ _ _ hstep
  · intro h
    have hjpre : j ∉ prefixList σ j k :=
      fun hj => (mem_prefixList_imp hj).1 rfl
    have hkpre : k ∉ prefixList σ j k :=
      fun hk => (mem_prefixList_imp hk).2 rfl
    rcases gameGraph_adj_cases_created (prefixList σ j k) j k
        hjpre hkpre hjk h with
      hpat | ⟨l₁, v, l₂, hl, hlegj, hlegk⟩
    · exact Or.inl hpat
    · refine Or.inr ⟨l₁, v, l₂ ++ σ.dropWhile
        (fun x => decide (x ≠ j ∧ x ≠ k)), ?_, ?_, ?_, ?_, ?_,
        hlegj, hlegk⟩
      · calc σ = prefixList σ j k ++ σ.dropWhile
              (fun x => decide (x ≠ j ∧ x ≠ k)) :=
            (List.takeWhile_append_dropWhile).symm
          _ = l₁ ++ v :: (l₂ ++ σ.dropWhile
              (fun x => decide (x ≠ j ∧ x ≠ k))) := by
            rw [hl, List.append_assoc, List.cons_append]
      · intro hj1
        exact hjpre (hl ▸ List.mem_append_left _ hj1)
      · intro hk1
        exact hkpre (hl ▸ List.mem_append_left _ hk1)
      · intro hjv
        exact hjpre (hl ▸ by
          rw [hjv]
          exact List.mem_append_right l₁ List.mem_cons_self)
      · intro hkv
        exact hkpre (hl ▸ by
          rw [hkv]
          exact List.mem_append_right l₁ List.mem_cons_self)



/-- `level_graph_path`: a level graph is path-determined and hence
depends only on the eliminated set (paper equation (1) and
Remark 2.8's justification that `G_S` is well defined). Proved as
`gameGraph_adj_iff_path` at the pattern graph. -/
theorem level_graph_path (l : List (Fin n)) (S : Finset (Fin n))
    (henum : Enumerates l S) (j k : Fin n) (hj : j ∉ S) (hk : k ∉ S)
    (hjk : j ≠ k) :
    ((gameGraph (patternGraph A) l).Adj j k ↔
      HasPathThrough (patternGraph A) S j k) :=
  gameGraph_adj_iff_path (patternGraph A) l S henum j k hj hk hjk



/-- `fill_path`: the fill-path theorem (paper Proposition 2.10,
`prop:fillpath`, proved there by citation of Rose, Tarjan and
Lueker): fill-graph membership, level-graph membership at the
committing prefix, and the path characterization agree. Proved
here rather than cited: (1)↔(2) is `fillGraph_adj_iff` (the
definition records the paper's observation that membership is
decided at the committing prefix), and (2)↔(3) is
`level_graph_path` at the prefix. Placed after `level_graph_path`
for dependency order. -/
theorem fill_path (σ : List (Fin n)) (hσ : IsOrdering σ)
    (j k : Fin n) (hjk : j ≠ k) :
    ((fillGraph A σ).Adj j k ↔
      (gameGraph (patternGraph A) (prefixList σ j k)).Adj j k) ∧
    ((gameGraph (patternGraph A) (prefixList σ j k)).Adj j k ↔
      HasPathThrough (patternGraph A) (prefixSet σ j k) j k) := by
  have hmem_tw : ∀ (l : List (Fin n)) (x : Fin n),
      x ∈ l.takeWhile (fun x => x ≠ j ∧ x ≠ k) → x ≠ j ∧ x ≠ k := by
    intro l
    induction l with
    | nil => intro x hx; exact (List.not_mem_nil hx).elim
    | cons y l ih =>
      intro x hx
      rw [List.takeWhile_cons] at hx
      by_cases hp : decide (y ≠ j ∧ y ≠ k) = true
      · rw [ite_eq_left hp] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact of_decide_eq_true hp
        · exact ih x hx
      · rw [ite_eq_right hp] at hx
        exact (List.not_mem_nil hx).elim
  have hnd : (prefixList σ j k).Nodup :=
    (List.takeWhile_sublist _).nodup hσ.1
  have henum : Enumerates (prefixList σ j k) (prefixSet σ j k) :=
    ⟨hnd, rfl⟩
  have hj : j ∉ prefixSet σ j k := by
    intro hj
    rw [prefixSet, prefixList, List.mem_toFinset] at hj
    exact (hmem_tw σ j hj).1 rfl
  have hk : k ∉ prefixSet σ j k := by
    intro hk
    rw [prefixSet, prefixList, List.mem_toFinset] at hk
    exact (hmem_tw σ k hk).2 rfl
  exact ⟨fillGraph_adj_iff σ j k,
    level_graph_path (prefixList σ j k) (prefixSet σ j k) henum j k hj
      hk hjk⟩

end CholeskyCancellations

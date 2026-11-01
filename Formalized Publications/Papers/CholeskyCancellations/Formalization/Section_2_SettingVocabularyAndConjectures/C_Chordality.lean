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
import Section_2_SettingVocabularyAndConjectures.B_PatternGraphs

/-! # Chordality vocabulary (paper Section 2)

Simplicial vertices, pendant vertices, perfect elimination orderings, chordal graphs, cut vertices, clique sums, and irreducibility (with `irreducible_iff_connected`). Split from `Defs.lean`.
-/

open scoped Matrix

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): vertices `Fin n`, SPD = `Matrix.PosDef`, levels `Finset (Fin n)`, pivot-order list orderings, Schur entries through `schurEntry` only. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}


/-- `IsSimplicial G v`: the neighborhood of `v` is a clique (paper
Definition 2.14, `def:graphvocab`). Mathlib has no simplicial
vocabulary; this is `SimpleGraph.IsClique` of the neighbor set. -/
def IsSimplicial (G : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  G.IsClique (G.neighborSet v)



/-- `IsPendant G v`: `v` has exactly one neighbor (paper
Definition 2.14, `def:graphvocab`). -/
def IsPendant (G : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  ∃! u : Fin n, G.Adj v u



/-- `AfterIn σ j k`: `k` comes after `j` in the ordering list `σ`. -/
def AfterIn (σ : List (Fin n)) (j k : Fin n) : Prop :=
  ∃ l₁ l₂ l₃ : List (Fin n), σ = l₁ ++ j :: l₂ ++ k :: l₃



/-- `IsPerfectEliminationOrdering G σ`: the later neighbors of every
vertex form a clique (paper Definition 2.14's PEO, `def:graphvocab`,
with "later" read in pivot order). -/
def IsPerfectEliminationOrdering (G : SimpleGraph (Fin n))
    (σ : List (Fin n)) : Prop :=
  IsOrdering σ ∧ ∀ j : Fin n,
    G.IsClique {k : Fin n | G.Adj j k ∧ AfterIn σ j k}



/-- `IsChordal G`: no induced subgraph is a chordless cycle of length
at least four (paper Definition 2.14, `def:graphvocab`). Mathlib has
no chordal graphs; an induced cycle is a `SimpleGraph.Walk.IsCycle`
in an induced subgraph whose whole edge set is the walk's edges (no
chord is present) and whose vertices all lie on the walk. -/
def IsChordal (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (s : Finset (Fin n)) (v : ↥(↑s : Set (Fin n)))
    (c : (G.induce (↑s : Set (Fin n))).Walk v v),
    c.IsCycle →
      (∀ e ∈ (G.induce (↑s : Set (Fin n))).edgeSet, e ∈ c.edges) →
        (↑s : Set (Fin n)) ⊆ Subtype.val '' {x | x ∈ c.support} →
          c.length < 4



/-- `IsCutVertex G v`: some reachable pair stops being reachable
once `v` is removed (paper Definition 2.14, `def:graphvocab`). -/
def IsCutVertex (G : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  ∃ a b : Fin n, a ≠ v ∧ b ≠ v ∧ G.Reachable a b ∧
    ∀ (ha : a ∈ ({v}ᶜ : Set (Fin n))) (hb : b ∈ ({v}ᶜ : Set (Fin n))),
      ¬ (G.induce ({v}ᶜ : Set (Fin n))).Reachable ⟨a, ha⟩ ⟨b, hb⟩



/-- `IsCliqueSumAlong G G₁ G₂ K`: `G` is the clique sum of `G₁` and
`G₂` along the clique `K` (paper Definition 2.14, `def:graphvocab`:
"`G = G₁ ∪ G₂` and `G₁ ∩ G₂ = K` is a clique"), read on a common
vertex set: `G = G₁ ⊔ G₂`, and the common edges of `G₁` and `G₂`
are exactly the pairs inside `K` (so `K` is a clique in each of
`G₁, G₂, G`). Gap: only the common-edge part of the paper's
`G₁ ∩ G₂ = K` is formalized. The vertex-set part is not: `G₁` and
`G₂` are spanning graphs on the same vertex set `Fin n`, so they
have no separate vertex sets whose intersection could be `K`
(the paper's `G₁, G₂` are subgraphs, not spanning graphs).
Modelling them as subgraphs would be needed to state that part.
The remaining vocabulary of Definition 2.14 — blocks and the
bipartite block-cut tree — is not formalized; no result in the
development uses it (the edge-disjoint-triangles proof works with
simplicial endpoints instead). -/
def IsCliqueSumAlong (G G₁ G₂ : SimpleGraph (Fin n)) (K : Finset (Fin n)) :
    Prop :=
  G = G₁ ⊔ G₂ ∧
    ∀ j k : Fin n, (G₁.Adj j k ∧ G₂.Adj j k) ↔ j ∈ K ∧ k ∈ K ∧ j ≠ k



/-- `IsIrreducible A`: no nontrivial partition of the vertices kills
every crossing entry (paper Definition 2.16, `def:irred`), stated in
negated form: every candidate partition has a nonzero crossing entry. -/
def IsIrreducible (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ V₁ V₂ : Finset (Fin n), V₁.Nonempty → V₂.Nonempty → Disjoint V₁ V₂ →
    V₁ ∪ V₂ = Finset.univ →
      ∃ i ∈ V₁, ∃ j ∈ V₂, A i j ≠ 0



/-- Irreducibility is connectedness of the pattern graph (paper
Proposition 2.17, `prop:irred-connected`). The conclusion is
literally Mathlib's `SimpleGraph.Connected` (preconnected plus a
vertex, supplied by `0 < n`); symmetry of `A` is the paper
Definition 2.16 hypothesis. -/
theorem irreducible_iff_connected (hn : 0 < n)
    (hsymm : ∀ i j : Fin n, A i j = A j i) :
    IsIrreducible A ↔ (patternGraph A).Connected := by
  classical
  rw [SimpleGraph.connected_iff]
  constructor
  · intro hIrr
    refine ⟨?_, ⟨⟨0, hn⟩⟩⟩
    intro u v
    by_cases hv : (patternGraph A).Reachable u v
    · exact hv
    · exfalso
      set S₁ := Finset.univ.filter
        (fun x => (patternGraph A).Reachable u x) with hS₁
      have hu : u ∈ S₁ := by simp [hS₁]
      obtain ⟨i, hi, j, hj, hij⟩ := hIrr S₁ S₁ᶜ ⟨u, hu⟩ ⟨v, by
        simp [hS₁, hv]⟩ (by simp [Finset.disjoint_iff_inter_eq_empty])
        (by simp)
      have hij_ne : i ≠ j := by
        rintro rfl
        exact (Finset.mem_compl.mp hj) hi
      have hadj : (patternGraph A).Adj i j := by
        simp [patternGraph, SimpleGraph.fromRel_adj, hij_ne, hij]
      have hri : (patternGraph A).Reachable u i := by simpa [hS₁] using hi
      have hrv : (patternGraph A).Reachable u j :=
        hri.trans hadj.reachable
      simp [hS₁, hrv] at hj
  · rintro ⟨hPre, -⟩ V₁ V₂ hV₁ hV₂ hdis hunion
    have key : ∀ {x y : Fin n} (w : (patternGraph A).Walk x y),
        x ∈ V₁ → y ∈ V₂ → ∃ i ∈ V₁, ∃ j ∈ V₂, A i j ≠ 0 := by
      intro x y w
      induction w with
      | nil => intro hx hy
               exact absurd hy (Finset.disjoint_left.mp hdis hx)
      | @cons a b c hadj w ih =>
          intro hx hy
          by_cases hz : b ∈ V₂
          · have hadj' : a ≠ b ∧ (A a b ≠ 0 ∨ A b a ≠ 0) := by
              simpa [patternGraph, SimpleGraph.fromRel_adj] using hadj
            rcases hadj'.2 with h1 | h1
            · exact ⟨_, hx, _, hz, h1⟩
            · exact ⟨_, hx, _, hz, by rw [hsymm]; exact h1⟩
          · have hz1 : b ∈ V₁ := by
              have hb : b ∈ V₁ ∪ V₂ := by
                rw [hunion]; exact Finset.mem_univ b
              rcases Finset.mem_union.mp hb with h1 | h1
              · exact h1
              · exact absurd h1 hz
            exact ih hz1 hy
    obtain ⟨a, ha⟩ := hV₁
    obtain ⟨b, hb⟩ := hV₂
    obtain ⟨w⟩ := hPre a b
    exact key w ha hb

end CholeskyCancellations

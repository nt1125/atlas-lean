/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/
import Mathlib

/-!
# Comparator challenge: Cholesky cancellations

Challenge module for the comparator (see
`cholesky_cancellations_comparator.json`). The definitions below are
stated independently in this file, by design: they must NOT be imported
from the solution (`Formalization/`), otherwise changing a solution
definition would change both sides of the comparison and the comparator
would certify nothing about the definitions themselves. They duplicate
the paper-facing definitions of the solution under the same names, and
every one of them is enumerated in `definition_names` in the JSON
config. The theorems are the paper-facing results, stated with these
challenge definitions and proved with `sorry` here; the comparator
checks that the solution proves the same statements (and uses the same
definitions) with only the permitted axioms.
-/

open scoped Matrix

namespace CholeskyCancellations

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}


/-- The survivor index type at level `S`: `R = V \ S`
(paper Definition 2.2). -/
abbrev Survivors (S : Finset (Fin n)) : Type :=
  ↥Sᶜ


/-- The index equivalence `S ⊕ (V \ S) ≃ V` used to read `A` in
`2×2` block form for Schur complement arguments. -/
noncomputable def sumComplEquiv (S : Finset (Fin n)) :
    (↥S ⊕ ↥Sᶜ) ≃ Fin n where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun i := if h : i ∈ S then Sum.inl ⟨i, h⟩
    else Sum.inr ⟨i, Finset.mem_compl.mpr h⟩
  left_inv x := by
    cases x with
    | inl a => simp [a.2]
    | inr a => simp [Finset.mem_compl.mp a.2]
  right_inv i := by by_cases h : i ∈ S <;> simp [h]


/-- `schurSet A S`: the Schur complement `A/A_S = A_RR - A_RS A_SS⁻¹ A_SR`
on the survivors `R = V \ S` (paper Definition 2.2, `def:spd-schur`).
Total by junk values, like `Matrix.inv`: if `A_SS` is singular the
inverse is `0`. -/
noncomputable def schurSet (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    Matrix (Survivors S) (Survivors S) ℝ :=
  let aRR : Matrix (Survivors S) (Survivors S) ℝ :=
    A.submatrix Subtype.val Subtype.val
  let aRS : Matrix (Survivors S) ↥S ℝ :=
    A.submatrix Subtype.val Subtype.val
  let aSS : Matrix ↥S ↥S ℝ :=
    A.submatrix Subtype.val Subtype.val
  let aSR : Matrix ↥S (Survivors S) ℝ :=
    A.submatrix Subtype.val Subtype.val
  aRR - aRS * aSS⁻¹ * aSR


/-- `schurEntry A S j k`: the entry `(A/A_S)_{jk}` (paper
Definition 2.2), read at plain vertices. Outside the survivors the
value is the junk value `0`; every use is guarded by `j ∉ S`, `k ∉ S`. -/
noncomputable def schurEntry (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (j k : Fin n) : ℝ :=
  if hj : j ∈ Sᶜ then
    if hk : k ∈ Sᶜ then schurSet A S ⟨j, hj⟩ ⟨k, hk⟩ else 0
  else 0


/-- `pivotEntry A S p j k`: the rank-one update value
`M_{jk} - M_{jp} M_{kp} / M_{pp}` for `M = A/A_S` (paper
Definition 2.6, `def:pivot`); `M_{jp}`, `M_{kp}` are its legs and
`M_{pp}` its pivot value. -/
noncomputable def pivotEntry (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p j k : Fin n) : ℝ :=
  schurEntry A S j k
    - schurEntry A S j p * schurEntry A S k p / schurEntry A S p p


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


variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}


/-- `Zeroes A S p j k`: the pivot at `p` at level `S` zeroes the pair
`{j, k}`, by the defining equation
`(A/A_S)_{pp} (A/A_S)_{jk} = (A/A_S)_{pj} (A/A_S)_{pk}`; `p` is then
the apex of the cancellation along the route `j-p-k` (paper
Definition 2.19, `def:cancel`). -/
def Zeroes (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p j k : Fin n) : Prop :=
  p ∉ S ∧ j ∉ insert p S ∧ k ∉ insert p S ∧ j ≠ k ∧
    schurEntry A S p p * schurEntry A S j k
      = schurEntry A S p j * schurEntry A S p k


/-- `cancellationGraph A S p`: the cancellation graph `C_p(S)` (paper
Definition 2.19, `def:cancel`), on the full vertex set; `Zeroes`
keeps it supported on the survivors of `S ∪ {p}`. -/
def cancellationGraph (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p : Fin n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun j k => Zeroes A S p j k


/-- `Covers A S p q`: `C_p(S)` covers `q` (paper Definition 2.19,
`def:cancel`). -/
def Covers (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p q : Fin n) : Prop :=
  ∃ k : Fin n, Zeroes A S p q k ∨ Zeroes A S p k q


/-- `Survives A S p q`: `q` survives the pivot at `p`, i.e. is not
covered (paper Definition 2.19, `def:cancel`). No survivor
hypothesis on `q` is included: the paper's `C_p(S)` contains
only pairs of survivors of `S ∪ {p}`, so for `q ∈ S ∪ {p}` no
pair of `C_p(S)` contains `q` and survival is vacuous, exactly
as `¬ Covers` says. -/
def Survives (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p q : Fin n) : Prop :=
  ¬ Covers A S p q


/-- `IsCleanPivotAt A l S p`: `p` is a clean pivot at level `S`
(enumerated by `l`): it destroys no predicted-nonzero pair (paper
Definition 2.19, `def:cancel`). The `Enumerates l S` conjunct is
load-bearing: the paper's `G_S` depends only on the level `S`,
and `gameGraph (patternGraph A) l` is `G_S` (between survivors)
only when `l` enumerates `S`; without it the same `(S, p)`
could get different verdicts for `l = []` versus an `l`
enumerating `S`. -/
def IsCleanPivotAt (A : Matrix (Fin n) (Fin n) ℝ) (l : List (Fin n))
    (S : Finset (Fin n)) (p : Fin n) : Prop :=
  Enumerates l S ∧ ∀ j k : Fin n, Zeroes A S p j k →
    ¬ (gameGraph (patternGraph A) l).Adj j k


/-- `IsCleanApexFor A S p T`: `p` is a clean apex for the triangle
`T`: `C_p(S)` contains no pair of `T` (paper Definition 2.19,
`def:cancel`). -/
def IsCleanApexFor (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p : Fin n) (T : Finset (Fin n)) : Prop :=
  ∀ j ∈ T, ∀ k ∈ T, ¬ Zeroes A S p j k


/-- `IsCleanApex A S p`: `C_p(S)` is empty (paper Definition 2.19,
`def:cancel`, the unqualified "clean apex"). -/
def IsCleanApex (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p : Fin n) : Prop :=
  ∀ j k : Fin n, ¬ Zeroes A S p j k


/-- `IsUniversalAt A S v`: `v` is universal in `A/A_S` — every other
survivor entry in its row is nonzero (paper Definition 2.21,
`def:universal`). -/
def IsUniversalAt (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (v : Fin n) : Prop :=
  v ∉ S ∧ ∀ j : Fin n, j ∉ S → j ≠ v → schurEntry A S v j ≠ 0


/-- `prefixListBefore σ p`: the vertices pivoted before `p` in `σ`
(paper Definition 2.23's `S_{j-1}` for `p = v_j`). -/
def prefixListBefore (σ : List (Fin n)) (p : Fin n) : List (Fin n) :=
  σ.takeWhile fun x => x ≠ p


/-- `factorEntry A σ p k`: the Cholesky factor entry `L_{kp}` by its
value `(A/A_{S})_{kp} / √(A/A_{S})_{pp}` at the level `S` preceding
`p` in `σ` (paper Definition 2.23, `def:Llink`). The assembled
matrix is `factorMatrix` below, proved to be the Cholesky factor
of `A` for the ordering `σ`: `factorMatrix_mul_transpose`,
`factorMatrix_eq_zero_of_afterIn`, `factorMatrix_diag`. -/
noncomputable def factorEntry (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : List (Fin n)) (p k : Fin n) : ℝ :=
  schurEntry A (prefixListBefore σ p).toFinset k p
    / Real.sqrt (schurEntry A (prefixListBefore σ p).toFinset p p)


/-- `factorMatrix A σ`: the assembled Cholesky factor `L`, with
`(k, p)` entry the factor entry `L_{kp}` of Definition 2.23. -/
noncomputable def factorMatrix (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : List (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun k p => factorEntry A σ p k


variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}


/-- `IsCleanOrdering A σ`: every predicted-nonzero position is nonzero
at its committing level (paper Definition 2.24, `def:clean`), the
factor notion of cleanliness. -/
def IsCleanOrdering (A : Matrix (Fin n) (Fin n) ℝ) (σ : List (Fin n)) :
    Prop :=
  ∀ j k : Fin n, PredictedNonzero A σ j k →
    schurEntry A (prefixSet σ j k) j k ≠ 0


/-- `IsFixedOrderingFor G σ`: one ordering chosen from the pattern
alone, clean for every SPD realization (paper Definition 2.25,
`def:strategy`). -/
def IsFixedOrderingFor (G : SimpleGraph (Fin n)) (σ : List (Fin n)) : Prop :=
  IsOrdering σ ∧ ∀ A : Matrix (Fin n) (Fin n) ℝ,
    A.PosDef → patternGraph A = G → IsCleanOrdering A σ


/-- `PatternAdmitsPerMatrixCleanOrdering G`: for every SPD
realization some (hence possibly matrix-dependent) ordering is
clean. This is the per-matrix existential reading of the paper's
"admits an adaptive clean ordering" (paper Definition 2.25,
`def:strategy`) — not the paper's strategy reading. It is
deliberately named for what it is: the ordering `σ` may be chosen
after seeing all of `A`, with no requirement that its pivots be
produced by one pivot-choice rule. The paper's Theorem 4.8 is
itself stated as "Conjecture 1 holds for …", i.e. in exactly
this per-matrix form, and `positives` proves this form. For the
paper's strategy form, see `PatternAdmitsAdaptiveStrategy`:
it is a priori more restrictive (a strategy must make the same next
choice for matrices agreeing up to the current level); whether it
is strictly stronger is not established here, and the
development does not prove it for any class. -/
def PatternAdmitsPerMatrixCleanOrdering (G : SimpleGraph (Fin n)) :
    Prop :=
  ∀ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef → patternGraph A = G →
    ∃ σ : List (Fin n), IsOrdering σ ∧ IsCleanOrdering A σ


/-- `schurMatrix A S`: the current Schur complement `A/A_S` as a
full matrix on `Fin n`, with entries `schurEntry A S j k` — the
only data an adaptive strategy may consult at level `S` (paper
Definition 2.25, `def:strategy`). -/
noncomputable def schurMatrix (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun j k => schurEntry A S j k


/-- `AdaptiveCleanStrategy G next`: `next` is an adaptive clean
strategy for the pattern `G` (paper Definition 2.25,
`def:strategy`). At each level `S`, `next` chooses the next pivot
as a function of `S` and the current Schur complement
`schurMatrix A S` alone — never of `A` itself — so two matrices
with the same Schur complement at `S` get the same next pivot
(consistency across matrices agreeing up to `S`). An ordering
`σ` follows `next` when every pivot `p` of `σ` is the choice
`next` makes at the level of the pivots preceding `p`. -/
def AdaptiveCleanStrategy (G : SimpleGraph (Fin n))
    (next : Finset (Fin n) → Matrix (Fin n) (Fin n) ℝ → Fin n) :
    Prop :=
  ∀ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef → patternGraph A = G →
    ∃ σ : List (Fin n), IsOrdering σ ∧ IsCleanOrdering A σ ∧
      ∀ (l₁ : List (Fin n)) (p : Fin n) (l₂ : List (Fin n)),
        σ = l₁ ++ p :: l₂ →
          p = next l₁.toFinset (schurMatrix A l₁.toFinset)


/-- `PatternAdmitsAdaptiveStrategy G`: some adaptive clean strategy
(as in `AdaptiveCleanStrategy`) yields a clean ordering for every
SPD realization of `G` — the paper's Definition 2.25 reading of
"admits an adaptive clean ordering". This is the paper's strategy
reading, a priori more restrictive than the per-matrix form;
`PatternAdmitsPerMatrixCleanOrdering` is what `positives`
proves. -/
def PatternAdmitsAdaptiveStrategy (G : SimpleGraph (Fin n)) : Prop :=
  ∃ next : Finset (Fin n) → Matrix (Fin n) (Fin n) ℝ → Fin n,
    AdaptiveCleanStrategy G next


variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}


/-- `FirstSchurClean A σ`: the first Schur complement along `σ` has
no cancellation at a predicted-nonzero position (paper
Conjecture 2.26's requirement, `conj:2`). Positions of the first
Schur complement are pairs of survivors, so `j` and `k` are
restricted away from the first pivot `p`. -/
def FirstSchurClean (A : Matrix (Fin n) (Fin n) ℝ) (σ : List (Fin n)) :
    Prop :=
  ∀ (p : Fin n) (l : List (Fin n)), σ = p :: l →
    ∀ j k : Fin n, j ≠ p → k ≠ p →
      (gameGraph (patternGraph A) [p]).Adj j k →
        schurEntry A {p} j k ≠ 0


/-- `first_schur_conjecture`: every irreducible SPD matrix admits an
ordering whose first Schur complement has no cancellation at a
predicted-nonzero position (paper Conjecture 2.26, `conj:2` —
"Conjecture 2" of Section 1.3; refuted at order 4 in the paper). -/
def first_schur_conjecture : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ),
    A.PosDef → IsIrreducible A →
      ∃ σ : List (Fin n), IsOrdering σ ∧ FirstSchurClean A σ


/-- `fill_graph_conjecture`: every irreducible SPD matrix admits a
clean ordering (paper Conjecture 2.27, `conj:1` — "Conjecture 1" of
Section 1.3; refuted at every even order at least 6 in the paper). -/
def fill_graph_conjecture : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ),
    A.PosDef → IsIrreducible A →
      ∃ σ : List (Fin n), IsOrdering σ ∧ IsCleanOrdering A σ


/-- A slot `(S, j, k)`: the formal demand `(A/A_S)_{jk} = 0` (paper
Definition 2.28, `def:slots`). -/
structure Slot (n : ℕ) where
  /-- The level of the slot (paper Definition 2.28). -/
  level : Finset (Fin n)
  /-- The first index of the demanded zero (paper Definition 2.28). -/
  fst : Fin n
  /-- The second index of the demanded zero (paper Definition 2.28). -/
  snd : Fin n
  /-- The first index survives the level (paper Definition 2.28). -/
  hf : fst ∉ level
  /-- The second index survives the level (paper Definition 2.28). -/
  hs : snd ∉ level
  /-- The two indices are distinct (paper Definition 2.28). -/
  hne : fst ≠ snd


/-- `Slot.Active A s`: the slot's demanded zero holds in `A` (paper
Definition 2.28, `def:slots`). -/
def Slot.Active (A : Matrix (Fin n) (Fin n) ℝ) (s : Slot n) : Prop :=
  schurEntry A s.level s.fst s.snd = 0


/-- `Slot.Spoils s A σ`: the slot spoils `σ` — its level is exactly
the committing prefix of its pair, which is predicted nonzero there
(paper Definition 2.29, `def:blocking`; prediction is read in the
paper's symbolic graph of `A`'s pattern). -/
def Slot.Spoils (s : Slot n) (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : List (Fin n)) : Prop :=
  s.level = prefixSet σ s.fst s.snd ∧
    (gameGraph (patternGraph A) (prefixList σ s.fst s.snd)).Adj
      s.fst s.snd


/-- `IsBlocking H G`: every ordering is spoiled by some slot of `H`,
for matrices of pattern `G` (paper Definition 2.29, `def:blocking`;
spoiling is evaluated against a chosen realization, whose pattern is
all that enters). -/
def IsBlocking (H : Set (Slot n)) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ A : Matrix (Fin n) (Fin n) ℝ, patternGraph A = G →
    ∀ σ : List (Fin n), IsOrdering σ → ∃ s ∈ H, s.Spoils A σ


/-- `IsRealizable H G`: some SPD matrix of pattern `G` makes every
slot of `H` active (paper Definition 2.29, `def:blocking`). -/
def IsRealizable (H : Set (Slot n)) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) ℝ,
    A.PosDef ∧ patternGraph A = G ∧ ∀ s ∈ H, s.Active A


/-- `partialCorr A S j k`: the partial correlation
`(A/A_S)_{jk} / √((A/A_S)_{jj} (A/A_S)_{kk})` (paper
Definition 2.32, `def:t`). Junk `0`-dividing values off the survivors
follow `schurEntry`. -/
noncomputable def partialCorr (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (j k : Fin n) : ℝ :=
  schurEntry A S j k
    / Real.sqrt (schurEntry A S j j * schurEntry A S k k)


/-- `logMag A S j k`: the log-magnitude `t⁽ˢ⁾_{jk} = -log |r⁽ˢ⁾_{jk}|`
(paper Definition 2.32, `def:t`). Totalisation: the paper puts
`t = +∞` at a zero entry, but `ℝ` has no `+∞`, so here `t` is
real-valued and totalised — at a zero entry
`partialCorr = 0`, `Real.log 0 = 0` in Lean, and `logMag = 0`,
not `+∞`. Every statement using `logMag` guards this away by
assuming the entries in play are nonzero (see `logMag_pos` and
`cancellation_additive`), where the two conventions agree and
`t > 0`; no lemma relies on the totalised value `0` at a zero
entry. An `Option`/`ENNReal` encoding would track `+∞`
faithfully but would complicate every arithmetic use, so the
totalisation is documented here instead. -/
noncomputable def logMag (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (j k : Fin n) : ℝ :=
  - Real.log |partialCorr A S j k|


/-- `IsFeasibleAt H S`: the additive system imposed by the slots of
`H` at the single level `S` has a strictly positive solution (paper
Definition 2.29, `def:blocking`). Each slot beyond `S` reading
`(S ∪ {v}, j, k)` imposes `t_{jk} = t_{vj} + t_{vk}` by the additive
lemma; here feasibility is stated directly for those equations. The
solution `t` is symmetric, as the paper's `t⁽ˢ⁾` is a function on
unordered pairs.

Formal-system caveat (paper Lemma 2.33, `lem:additive`): this
definition is matrix-free, so each slot imposes its equation
unconditionally, as a formal equation. The paper's lemma supplies
that equation from a realizing matrix only when both legs
`(A/A_S)_{vj}`, `(A/A_S)_{vk}` are nonzero — a hypothesis this
definition cannot state, having no matrix. Hence
`¬ IsFeasibleAt H S` (formal infeasibility) does not by itself
refute realizability: dropping the equations of zero-leg slots
could leave a feasible system. The correct bridge is
`feasible_of_active_of_legs_ne` below: active slots with
nonzero legs do imply feasibility, with `t` the log-magnitudes
of `A/A_S`. In particular the `¬ IsFeasibleAt` conclusions of
`general_cycle` and `four_cycle_infeasible` are formal-system
infeasibility, and no result in the development uses them to
conclude `¬ IsRealizable`. The Pairing Lemma's use of
`IsFeasibleAt` is likewise about the formal system, matching
the paper's "a slot imposes the relation" reading there. -/
def IsFeasibleAt (H : Set (Slot n)) (S : Finset (Fin n)) : Prop :=
  ∃ t : Fin n → Fin n → ℝ,
    (∀ j k : Fin n, 0 < t j k) ∧ (∀ j k : Fin n, t j k = t k j) ∧
    ∀ s ∈ H, ∃ v : Fin n, s.level = insert v S ∧ v ∉ S ∧
      t s.fst s.snd = t v s.fst + t v s.snd


variable {n : ℕ}


/-- `NonzeroPairs A S`: ordered representatives of the survivor
pairs nonzero in `A/A_S` — the vertices of the arc digraph (paper
Definition 3.15, `def:arcdigraph`). Bridge: the paper's vertices are
unordered pairs `{j, k}`; each appears here in both orders, and the
arc relation below is blind to the order chosen. -/
def NonzeroPairs (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : Type :=
  {p : Fin n × Fin n // p.1 ∉ S ∧ p.2 ∉ S ∧ p.1 ≠ p.2 ∧
    schurEntry A S p.1 p.2 ≠ 0}


/-- `SamePair x y u v`: `(x, y)` and `(u, v)` name the same unordered
pair (used by `arcDigraph`, paper Definition 3.15). -/
def SamePair (x y u v : Fin n) : Prop :=
  (x = u ∧ y = v) ∨ (x = v ∧ y = u)


/-- `arcDigraph A S H`: the arc digraph `D(H)` (paper
Definition 3.15, `def:arcdigraph`): an imposed relation
`t⁽ˢ⁾_{jk} = t⁽ˢ⁾_{ji} + t⁽ˢ⁾_{ki}` contributes the arcs
`{j, k} → {j, i}` and `{j, k} → {k, i}` between nonzero pairs. -/
noncomputable def arcDigraph (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (H : Set (Slot n)) : Digraph (NonzeroPairs A S) :=
  ⟨fun a b => ∃ s ∈ H, ∃ v : Fin n, s.level = insert v S ∧ v ∉ S ∧
    SamePair a.1.1 a.1.2 s.fst s.snd ∧
      (SamePair b.1.1 b.1.2 s.fst v ∨ SamePair b.1.1 b.1.2 s.snd v)⟩


variable {n : ℕ}


/-- The almost-principal submatrix on rows `S ∪ {j}`, columns
`S ∪ {k}`, indexed by `Option ↥S` with `none` for `j`/`k`. This is
the numerator matrix in the Jones–West determinant formula behind
the forest theorem (paper Theorem 4.1 proof). -/
noncomputable def almostPrincipal (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (j k : Fin n) :
    Matrix (Option ↥S) (Option ↥S) ℝ :=
  fun r c => A (match r with | none => j | some s => s.val)
    (match c with | none => k | some s => s.val)


/-- Reindexing equivalence `Option ↥S ≃ ↥S ⊕ Unit`. -/
def optionSumEquiv (S : Finset (Fin n)) : Option ↥S ≃ ↥S ⊕ Unit where
  toFun := fun o => match o with
    | none => Sum.inr ()
    | some s => Sum.inl s
  invFun := fun s => match s with
    | Sum.inl s => some s
    | Sum.inr _ => none
  left_inv := fun o => by cases o <;> rfl
  right_inv := fun s => by cases s <;> rfl


/-- Equivalence between `↥S` and `Option ↥(S \ {w})` sending `w` to `none`. -/
def sdiffOneEquiv (S : Finset (Fin n)) (w : Fin n) (hw : w ∈ S) :
    ↥S ≃ Option ↥(S \ {w}) where
  toFun := fun s => if h : s = ⟨w, hw⟩ then none
    else some ⟨s.val, Finset.mem_sdiff.mpr ⟨s.2,
      by simp only [Finset.notMem_singleton]; exact fun hh => h (Subtype.ext hh)⟩⟩
  invFun := fun o => match o with
    | none => ⟨w, hw⟩
    | some t => ⟨t.val, (Finset.mem_sdiff.mp t.2).1⟩
  left_inv := by
    intro s
    by_cases hs : s = ⟨w, hw⟩ <;> simp [hs]
  right_inv := by
    intro o
    cases o with
    | none => simp
    | some t =>
        have hne : (⟨t.val, (Finset.mem_sdiff.mp t.2).1⟩ : ↥S) ≠ ⟨w, hw⟩ := by
          simp only [ne_eq, Subtype.mk.injEq]
          exact fun hh => by
            have h2 := (Finset.mem_sdiff.mp t.2).2
            simp [hh] at h2
        simp [hne]


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


variable {n : ℕ}


/-- `ExactlyOneTriangle G`: `G` has exactly one triangle (3-clique)
(paper Theorem 4.8 (ii), `thm:positives`). -/
def ExactlyOneTriangle (G : SimpleGraph (Fin n)) : Prop :=
  {T : Finset (Fin n) | T.card = 3 ∧ G.IsClique (↑T : Set (Fin n))}.ncard
    = 1


/-- `TrianglesEdgeDisjoint G`: distinct triangles of `G` share at
most one vertex, i.e. no edge (paper Theorem 4.8 (iii),
`thm:positives`). -/
def TrianglesEdgeDisjoint (G : SimpleGraph (Fin n)) : Prop :=
  ∀ T₁ T₂ : Finset (Fin n),
    T₁.card = 3 → G.IsClique (↑T₁ : Set (Fin n)) →
      T₂.card = 3 → G.IsClique (↑T₂ : Set (Fin n)) →
        T₁ ≠ T₂ → (T₁ ∩ T₂).card ≤ 1


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


variable {n : ℕ}


/-- `IsChordalState A lS S`: at level `S` (enumerated by `lS`) no
fill or cancellation has occurred yet: the game graph and the
numeric pattern on survivors both agree with `patternGraph A`.
State for the induction proving paper Theorem 4.8 (iii),
`thm:positives`. -/
def IsChordalState (A : Matrix (Fin n) (Fin n) ℝ)
    (lS : List (Fin n)) (S : Finset (Fin n)) : Prop :=
  Enumerates lS S ∧
    (∀ x y : Fin n, x ∉ S → y ∉ S → x ≠ y →
      ((gameGraph (patternGraph A) lS).Adj x y ↔
        (patternGraph A).Adj x y)) ∧
    (∀ x y : Fin n, x ∉ S → y ∉ S → x ≠ y →
      (schurEntry A S x y ≠ 0 ↔ (patternGraph A).Adj x y))


variable {n : ℕ}


/-- `astar`: the order-four matrix
`[[4,-2,-2,-1],[-2,4,1,2],[-2,1,4,2],[-1,2,2,4]]` (paper
Theorem 5.1, `thm:Astar`). -/
def astar : Matrix (Fin 4) (Fin 4) ℝ :=
  !![4, -2, -2, -1; -2, 4, 1, 2; -2, 1, 4, 2; -1, 2, 2, 4]


/-- `astarP`: the eigenbasis matrix for `astar`, with columns
`(1,-1,-1,-1)`, `(1,1,1,-1)`, `(0,1,-1,0)` and `(1,0,0,1)`, of
eigenvalues `9, 1, 3, 3`. Its columns are mutually orthogonal. -/
def astarP : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of ![
  ![1, 1, 0, 1],
  ![-1, 1, 1, 0],
  ![-1, 1, -1, 0],
  ![-1, -1, 0, 1]]


/-- The partnership involution `(0 3)(1 2)` on the four indices of
`astar`. -/
def astarPartner (x : Fin 4) : Fin 4 := ![3, 2, 1, 0] x


variable {n : ℕ}


/-- `IsFixedPointFreeInvolution π`: `π` is a fixed-point-free
involution (paper Definition 5.4, `def:involution`); on a foursome
these are exactly the three pairings. -/
def IsFixedPointFreeInvolution {α : Type*} (π : Equiv.Perm α) : Prop :=
  Function.Involutive π ∧ ∀ x : α, π x ≠ x


/-- `CandidateSlot S W s`: `s` is one of the candidate slots at a
four-survivor level — an apex in `W` cancelling a pair inside `W`
(paper Lemma 5.5, `lem:pairing`). The paper writes such a slot as
`(u, {j, k})`, with an unordered cancelled pair; the increasing
orientation `s.fst < s.snd` is the canonical representative of that
pair among ordered slots. -/
def CandidateSlot (S W : Finset (Fin n)) (s : Slot n) : Prop :=
  s.fst < s.snd ∧ ∃ u ∈ W, s.level = insert u S ∧ s.fst ∈ W ∧
    s.snd ∈ W ∧ s.fst ≠ u ∧ s.snd ≠ u


/-- `PairingConfig π S W H`: `H` is the slot configuration of a
fixed-point-free involution `π` of `W` (here `π` is a plain function
involutive and fixed-point-free on `W`): each vertex of `W` cancels
the pair opposite its own, and every slot of `H` has that form
(paper Lemma 5.5, `lem:pairing`). -/
def PairingConfig (π : Fin n → Fin n) (S W : Finset (Fin n))
    (H : Set (Slot n)) : Prop :=
  (∀ u ∈ W, π u ∈ W ∧ π (π u) = u ∧ π u ≠ u) ∧
    (∀ u ∈ W, ∃ s ∈ H, s.level = insert u S ∧
      ({s.fst, s.snd} : Finset (Fin n)) = (W.erase u).erase (π u)) ∧
    ∀ s ∈ H, ∃ u ∈ W, s.level = insert u S ∧
      ({s.fst, s.snd} : Finset (Fin n)) = (W.erase u).erase (π u)


noncomputable def slotApexOf {n : ℕ} (S W : Finset (Fin n)) (a0 : Fin n) (s : Slot n) : Fin n :=
  if h : ∃ u ∈ W, s.level = insert u S ∧ s.fst ∈ W ∧ s.snd ∈ W ∧
      s.fst ≠ u ∧ s.snd ≠ u then Classical.choose h else a0


noncomputable def slotMissingOf {n : ℕ} (S W : Finset (Fin n)) (a0 : Fin n) (s : Slot n) : Fin n :=
  if h : ∃ d : Fin n, d ∈ W ∧ d ≠ slotApexOf S W a0 s ∧ d ≠ s.fst ∧ d ≠ s.snd then
    Classical.choose h else a0


variable {n : ℕ}
variable {m : ℕ} {a b : ℝ}


/-- `m2mMatrix m a b`: the matrix `M_{2m}` — unit diagonal, `a * b`
inside each pair `P_k = {2k, 2k+1}`, `a` across pairs at equal
parity, `b` across pairs at opposite parity (paper Theorem 5.8,
`thm:M2m`). -/
def m2mMatrix (m : ℕ) (a b : ℝ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  fun x y =>
    if x = y then 1
    else if x.val / 2 = y.val / 2 then a * b
    else if x.val % 2 = y.val % 2 then a
    else b


/-- Partner of a vertex in its pair `P_k = {2k, 2k+1}`. -/
def m2mPartner (x : Fin (2 * m)) : Fin (2 * m) :=
  if _h : x.val % 2 = 0 then ⟨x.val + 1, by have hx := x.2; omega⟩
  else ⟨x.val - 1, by have hx := x.2; omega⟩


variable {n : ℕ}
variable {m : ℕ} {a b : ℝ}


/-- The orthogonal zero-sum weights `w_k` on pair indices:
`w_k = (1, …, 1, -k, 0, …, 0)` with `k` ones. -/
def m2mW (k t : ℕ) : ℝ :=
  if t < k then 1 else if t = k then -(k : ℝ) else 0


/-- Pair-major indexing equivalence `Fin m × Fin 2 ≃ Fin (2m)`. -/
def m2mVertexEquiv (m : ℕ) : Fin m × Fin 2 ≃ Fin (2 * m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))


/-- The vertex `2t + e` in pair `t` at parity `e`. -/
def m2mVertex (t : Fin m) (e : Fin 2) : Fin (2 * m) :=
  m2mVertexEquiv m (t, e)


/-- The pair index of a vertex, as an element of `Fin m`. -/
def m2mPair (x : Fin (2 * m)) : Fin m :=
  ⟨x.val / 2, by have hx := x.2; omega⟩


/-- Parity sign of a vertex. -/
def m2mSign (x : Fin (2 * m)) : ℝ := if x.val % 2 = 0 then 1 else -1


/-- Pair-sum coordinates of the eigenbasis columns. -/
def m2mU (c : Fin (2 * m)) (t : Fin m) : ℝ :=
  if c.val = 0 then 1
  else if c.val = 1 then 0
  else if c.val % 2 = 0 then m2mW (c.val / 2) t.val
  else 0


/-- Pair-difference coordinates of the eigenbasis columns. -/
def m2mV (c : Fin (2 * m)) (t : Fin m) : ℝ :=
  if c.val = 0 then 0
  else if c.val = 1 then 1
  else if c.val % 2 = 0 then 0
  else m2mW (c.val / 2) t.val


/-- `m2mP m`: the (orthogonal) eigenbasis matrix for `M_{2m}`:
column `0` is all-ones, column `1` is the parity sign, columns
`2k`/`2k+1` for `k ≥ 1` are the pair-sum/pair-difference lifts of
`w_k`. -/
def m2mP (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  fun x c => m2mU c (m2mPair x) + m2mSign x * m2mV c (m2mPair x)


/-- The eigenvalue of column `c` of `m2mP m`. -/
def m2mEigen (m : ℕ) (a b : ℝ) (c : Fin (2 * m)) : ℝ :=
  if c.val = 0 then 1 + a * b + (a + b) * ((m : ℝ) - 1)
  else if c.val = 1 then 1 - a * b + (a - b) * ((m : ℝ) - 1)
  else if c.val % 2 = 0 then (1 - a) * (1 - b)
  else (1 - a) * (1 + b)


/-- Squared norm of column `c` of `m2mP m`. -/
def m2mNorm (c : Fin (2 * m)) : ℝ :=
  ∑ x, m2mP m x c * m2mP m x c


variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {m : ℕ} {a b : ℝ}


theorem astar_counts :
    astar.PosDef ∧
      astar.charpoly
        = (Polynomial.X - Polynomial.C 9) * (Polynomial.X - Polynomial.C 3) ^ 2
          * (Polynomial.X - Polynomial.C 1) ∧
      (∀ σ : List (Fin 4), IsOrdering σ → ¬ FirstSchurClean astar σ) ∧
      {σ : List (Fin 4) | IsOrdering σ ∧ IsCleanOrdering astar σ}.ncard = 8 := by
  sorry


theorem astar_irreducible : IsIrreducible astar := by
  sorry


theorem astar_posDef : astar.PosDef := by
  sorry


theorem cancellation_additive (hA : A.PosDef) (S : Finset (Fin n))
    (v j k : Fin n) (hv : v ∉ S) (hj : j ∉ insert v S)
    (hk : k ∉ insert v S) (hlegj : schurEntry A S v j ≠ 0)
    (hlegk : schurEntry A S v k ≠ 0) :
    (schurEntry A (insert v S) j k = 0 ↔
      partialCorr A S j k
        = partialCorr A S v j * partialCorr A S v k) ∧
    (schurEntry A (insert v S) j k = 0 →
      logMag A S j k = logMag A S v j + logMag A S v k) ∧
    (logMag A S j k = logMag A S v j + logMag A S v k →
      0 < partialCorr A S j k
          * (partialCorr A S v j * partialCorr A S v k) →
        schurEntry A (insert v S) j k = 0) := by
  sorry


theorem clean_of_order_le_four : ∀ {n : ℕ}, n ≤ 4 →
    ∀ A : Matrix (Fin n) (Fin n) ℝ,
    A.PosDef → IsIrreducible A →
      ∃ σ : List (Fin n), IsOrdering σ ∧ IsCleanOrdering A σ := by
  sorry


theorem dense_safety (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (S : Finset (Fin n))
    (hdense : ∀ j k : Fin n, j ∉ S → k ∉ S → j ≠ k →
      schurEntry A S j k ≠ 0)
    (p q : Fin n) (hp : p ∉ S) (hq : q ∉ S) (hpq : p ≠ q)
    (hmax : ∀ j k : Fin n, j ∉ S → k ∉ S → j ≠ k →
      logMag A S j k ≤ logMag A S p q) :
    ¬ Covers A S p q := by
  sorry


theorem exchange (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (u j k : Fin n) (huj : u ≠ j) (_huk : u ≠ k) (_hjk : j ≠ k)
    (hak : A u k ≠ 0) (h1 : A u u * A j k = A u j * A u k) :
    A j j * A u k ≠ A j u * A j k := by
  sorry


theorem factorEntry_ne_zero_iff (hA : A.PosDef) (σ : List (Fin n))
    (p k : Fin n) :
    factorEntry A σ p k ≠ 0 ↔
      schurEntry A (prefixListBefore σ p).toFinset k p ≠ 0 := by
  sorry


theorem factorMatrix_diag (hA : A.PosDef) (σ : List (Fin n))
    (p : Fin n) :
    factorMatrix A σ p p
      = Real.sqrt (schurEntry A (prefixListBefore σ p).toFinset p p) ∧
    0 < factorMatrix A σ p p := by
  sorry


theorem factorMatrix_eq_zero_of_afterIn {σ : List (Fin n)}
    (hσ : IsOrdering σ) {k p : Fin n} (h : AfterIn σ k p) :
    factorMatrix A σ k p = 0 := by
  sorry


theorem factorMatrix_mul_transpose (hA : A.PosDef)
    (σ : List (Fin n)) (hσ : IsOrdering σ) :
    factorMatrix A σ * (factorMatrix A σ)ᵀ = A := by
  sorry


theorem factorPattern_adj_iff_factorEntry (hA : A.PosDef)
    (σ : List (Fin n)) (hσ : IsOrdering σ) {j k : Fin n}
    (hafter : AfterIn σ j k) :
    (factorPattern A σ).Adj j k ↔ factorEntry A σ j k ≠ 0 := by
  sorry


theorem fillGraphGame_adj_iff {A : Matrix (Fin n) (Fin n) ℝ}
    {σ : List (Fin n)} {j k : Fin n} (hjk : j ≠ k) :
    (fillGraphGame A σ).Adj j k ↔
      (patternGraph A).Adj j k ∨
      ∃ (l : List (Fin n)) (v : Fin n) (t : List (Fin n)),
        σ = l ++ v :: t ∧ j ∉ l ∧ k ∉ l ∧ j ≠ v ∧ k ≠ v ∧
        (gameGraph (patternGraph A) l).Adj j v ∧
        (gameGraph (patternGraph A) l).Adj k v := by
  sorry


theorem fillGraphGame_eq_fillGraph (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : List (Fin n)) (hσ : IsOrdering σ) :
    fillGraphGame A σ = fillGraph A σ := by
  sorry


theorem fill_graph_conjecture_refuted : ¬ fill_graph_conjecture := by
  sorry


theorem fill_path (σ : List (Fin n)) (hσ : IsOrdering σ)
    (j k : Fin n) (hjk : j ≠ k) :
    ((fillGraph A σ).Adj j k ↔
      (gameGraph (patternGraph A) (prefixList σ j k)).Adj j k) ∧
    ((gameGraph (patternGraph A) (prefixList σ j k)).Adj j k ↔
      HasPathThrough (patternGraph A) (prefixSet σ j k) j k) := by
  sorry


theorem fill_path_example {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A.PosDef) (h01 : (patternGraph A).Adj 0 1)
    (h12 : (patternGraph A).Adj 1 2)
    (h02 : ¬ (patternGraph A).Adj 0 2) :
    (gameGraph (patternGraph A) [1]).Adj 0 2 ∧
    (fillGraph A [1, 0, 2]).Adj 0 2 ∧
    schurEntry A {1} 0 2 = -A 0 1 * A 1 2 / A 1 1 ∧
    schurEntry A {1} 0 2 ≠ 0 := by
  sorry


theorem first_schur_conjecture_refuted : ¬ first_schur_conjecture := by
  sorry


theorem forest_clean {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hF : (patternGraph A).IsAcyclic) (σ : List (Fin n))
    (hσ : IsOrdering σ) : IsCleanOrdering A σ := by
  sorry


theorem four_cycle (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (S : Finset (Fin n)) (a b c d : Fin n)
    (ha : a ∉ S) (hb : b ∉ S) (hc : c ∉ S) (hd : d ∉ S)
    (hac : a ≠ c) (hbd : b ≠ d)
    (hne : ∀ x ∈ ({a, b, c, d} : Finset (Fin n)),
      ∀ y ∈ ({a, b, c, d} : Finset (Fin n)), x ≠ y →
        schurEntry A S x y ≠ 0) :
    ¬ (logMag A S a b = logMag A S a c + logMag A S b c
      ∧ logMag A S b c = logMag A S b d + logMag A S c d
      ∧ logMag A S c d = logMag A S c a + logMag A S d a
      ∧ logMag A S d a = logMag A S d b + logMag A S a b) := by
  sorry


theorem four_cycle_infeasible {S : Finset (Fin n)} {a b c d : Fin n}
    (ha : a ∉ S) (hb : b ∉ S) (hc : c ∉ S) (hd : d ∉ S)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ¬ IsFeasibleAt
      {⟨insert c S, a, b,
          (by rw [Finset.mem_insert]; push Not; exact ⟨hac, ha⟩),
          (by rw [Finset.mem_insert]; push Not; exact ⟨hbc, hb⟩), hab⟩,
        ⟨insert d S, b, c,
          (by rw [Finset.mem_insert]; push Not; exact ⟨hbd, hb⟩),
          (by rw [Finset.mem_insert]; push Not; exact ⟨hcd, hc⟩), hbc⟩,
        ⟨insert a S, c, d,
          (by rw [Finset.mem_insert]; push Not; exact ⟨fun h => hac h.symm, hc⟩),
          (by rw [Finset.mem_insert]; push Not; exact ⟨fun h => had h.symm, hd⟩),
          hcd⟩,
        ⟨insert b S, d, a,
          (by rw [Finset.mem_insert]; push Not; exact ⟨fun h => hbd h.symm, hd⟩),
          (by rw [Finset.mem_insert]; push Not; exact ⟨hab, ha⟩),
          Ne.symm had⟩} S := by
  sorry


theorem fresh_fill (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (l : List (Fin n)) (S : Finset (Fin n)) (henum : Enumerates l S)
    (v j k : Fin n) (hv : v ∉ S) (hj : j ∉ insert v S)
    (hk : k ∉ insert v S) (hjk : j ≠ k)
    (_hjv : (gameGraph (patternGraph A) l).Adj j v)
    (_hkv : (gameGraph (patternGraph A) l).Adj k v)
    (hnk : ¬ (gameGraph (patternGraph A) l).Adj j k) :
    schurEntry A S j k = 0 ∧
    schurEntry A (insert v S) j k
      = - (schurEntry A S j v * schurEntry A S k v
          / schurEntry A S v v) ∧
    (schurEntry A S j v ≠ 0 → schurEntry A S k v ≠ 0 →
      schurEntry A (insert v S) j k ≠ 0) := by
  sorry


theorem fresh_fill_closure (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (l : List (Fin n)) (S : Finset (Fin n))
    (henum : Enumerates l S) (v j k : Fin n) (hv : v ∉ S)
    (hj : j ∉ insert v S) (hk : k ∉ insert v S) (hjk : j ≠ k)
    (_hjv : (gameGraph (patternGraph A) l).Adj j v)
    (_hkv : (gameGraph (patternGraph A) l).Adj k v)
    (hnk : ¬ (gameGraph (patternGraph A) l).Adj j k)
    (hz : schurEntry A (insert v S) j k = 0) :
    schurEntry A S j v = 0 ∨ schurEntry A S k v = 0 := by
  sorry


theorem general_cycle (A : Matrix (Fin n) (Fin n) ℝ) (_hA : A.PosDef)
    (S : Finset (Fin n)) (H : Set (Slot n))
    (_hslots : ∀ s ∈ H, ∃ v : Fin n, v ∉ S ∧ s.level = insert v S)
    (hcycle : ∃ a : NonzeroPairs A S,
      Relation.TransGen (arcDigraph A S H).Adj a a) :
    ¬ IsFeasibleAt H S := by
  sorry


theorem irreducible_iff_connected (hn : 0 < n)
    (hsymm : ∀ i j : Fin n, A i j = A j i) :
    IsIrreducible A ↔ (patternGraph A).Connected := by
  sorry


theorem m2mMatrix_irreducible {m : ℕ} {a b : ℝ}
    (hb : 0 < b) (hba : b < a) :
    IsIrreducible (m2mMatrix m a b) := by
  sorry


theorem m2m_counterexample : ∀ (m : ℕ) (a b : ℝ), 2 ≤ m →
    a ^ 2 + (1 - b ^ 2) * a - 1 = 0 → 0 < b → b < a → a < 1 →
      (m2mMatrix m a b).PosDef ∧
        (m2mMatrix m a b).charpoly
          = (Polynomial.X - Polynomial.C (1 + a * b + (a + b) * ((m : ℝ) - 1)))
            * (Polynomial.X - Polynomial.C (1 - a * b + (a - b) * ((m : ℝ) - 1)))
            * (Polynomial.X - Polynomial.C ((1 - a) * (1 - b))) ^ (m - 1)
            * (Polynomial.X - Polynomial.C ((1 - a) * (1 + b))) ^ (m - 1) ∧
        0 < 1 + a * b + (a + b) * ((m : ℝ) - 1) ∧
        0 < 1 - a * b + (a - b) * ((m : ℝ) - 1) ∧
        0 < (1 - a) * (1 - b) ∧ 0 < (1 - a) * (1 + b) ∧
        (3 ≤ m → ∀ σ : List (Fin (2 * m)), IsOrdering σ →
          ¬ IsCleanOrdering (m2mMatrix m a b) σ) := by
  sorry


theorem m2m_counterexample_all_orders (m : ℕ) (hm : 3 ≤ m) :
    ∃ A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ,
      A.PosDef ∧ IsIrreducible A ∧
        ∀ σ : List (Fin (2 * m)), IsOrdering σ →
          ¬ IsCleanOrdering A σ := by
  sorry


theorem m2m_curve_instance :
    ∃ a b : ℝ, a ^ 2 + (1 - b ^ 2) * a - 1 = 0 ∧ 0 < b ∧ b < a ∧
      a < 1 := by
  sorry


theorem m2m_posDef (hm : 2 ≤ m) (hb : 0 < b) (hba : b < a)
    (ha1 : a < 1) : (m2mMatrix m a b).PosDef := by
  sorry


theorem magnitudes_converse (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ A : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℝ, A.PosDef ∧
      logMag A ∅ 0 2 = α ∧ logMag A ∅ 1 3 = α ∧
      logMag A ∅ 0 3 = β ∧ logMag A ∅ 1 2 = β ∧
      logMag A ∅ 0 1 = α + β ∧ logMag A ∅ 2 3 = α + β := by
  sorry


theorem magnitudes_forced {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (S : Finset (Fin n)) (w₀ w₁ w₂ w₃ : Fin n)
    (h0 : w₀ ∉ S) (h1 : w₁ ∉ S) (h2 : w₂ ∉ S) (h3 : w₃ ∉ S)
    (h01 : w₀ ≠ w₁) (h02 : w₀ ≠ w₂) (h03 : w₀ ≠ w₃)
    (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h23 : w₂ ≠ w₃)
    (hall : ∀ x ∈ ({w₀, w₁, w₂, w₃} : Finset (Fin n)),
      ∀ y ∈ ({w₀, w₁, w₂, w₃} : Finset (Fin n)), x ≠ y →
        schurEntry A S x y ≠ 0)
    (e1 : logMag A S w₂ w₃ = logMag A S w₀ w₂ + logMag A S w₀ w₃)
    (e2 : logMag A S w₂ w₃ = logMag A S w₁ w₂ + logMag A S w₁ w₃)
    (e3 : logMag A S w₀ w₁ = logMag A S w₀ w₂ + logMag A S w₁ w₂)
    (e4 : logMag A S w₀ w₁ = logMag A S w₀ w₃ + logMag A S w₁ w₃) :
    logMag A S w₀ w₂ = logMag A S w₁ w₃ ∧
    logMag A S w₀ w₃ = logMag A S w₁ w₂ ∧
    logMag A S w₀ w₁ = logMag A S w₀ w₂ + logMag A S w₀ w₃ ∧
    logMag A S w₂ w₃ = logMag A S w₀ w₂ + logMag A S w₀ w₃ ∧
    ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 0 < b ∧ b < 1 ∧
      |partialCorr A S w₀ w₂| = a ∧
      |partialCorr A S w₁ w₃| = a ∧
      |partialCorr A S w₀ w₃| = b ∧
      |partialCorr A S w₁ w₂| = b ∧
      |partialCorr A S w₀ w₁| = a * b ∧
      |partialCorr A S w₂ w₃| = a * b := by
  sorry


theorem max_edge (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hdense : ∀ i j : Fin n, i ≠ j → A i j ≠ 0)
    (p q : Fin n) (hpq : p ≠ q)
    (hmax : ∀ i j : Fin n, i ≠ j → logMag A ∅ i j ≤ logMag A ∅ p q) :
    ¬ Covers A ∅ p q ∧ Survives A ∅ p q := by
  sorry


theorem monotone (G : SimpleGraph (Fin n)) (H H' : Set (Slot n))
    (hHH' : H ⊆ H') (hH : ¬ IsRealizable H G) : ¬ IsRealizable H' G := by
  sorry


theorem nesting (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (S : Finset (Fin n)) (i j k : Fin n)
    (hi : i ∉ S) (hj : j ∉ S) (hk : k ∉ S) (hij : i ≠ j) (hik : i ≠ k)
    (_hjk : j ≠ k) (h0 : schurEntry A S j k = 0)
    (h1 : schurEntry A (insert i S) j k = 0) :
    schurEntry A S j i = 0 ∨ schurEntry A S k i = 0 := by
  sorry


theorem pairing (S W : Finset (Fin n)) (hW : W.card = 4)
    (hWS : ∀ u ∈ W, u ∉ S) :
    (∀ H : Set (Slot n), (∀ s ∈ H, CandidateSlot S W s) →
        IsFeasibleAt H S → H.ncard ≤ 4)
      ∧ (∀ H : Set (Slot n), (∀ s ∈ H, CandidateSlot S W s) →
          IsFeasibleAt H S → H.ncard = 4 →
            (∀ u ∈ W, ∃ s ∈ H, s.level = insert u S) →
              ∃ π : Fin n → Fin n, PairingConfig π S W H)
      ∧ (∀ π : Fin n → Fin n, ∀ H : Set (Slot n),
          (∀ s ∈ H, CandidateSlot S W s) → PairingConfig π S W H →
            IsFeasibleAt H S) := by
  sorry


theorem positives :
    (∀ {n : ℕ} (G : SimpleGraph (Fin n)), IsStripPattern G →
      PatternAdmitsPerMatrixCleanOrdering G)
    ∧ (∀ {n : ℕ} (G : SimpleGraph (Fin n)), IsFanPattern G →
        PatternAdmitsPerMatrixCleanOrdering G)
    ∧ (∀ {n : ℕ} (G : SimpleGraph (Fin n)),
        IsChordal G → ExactlyOneTriangle G → PatternAdmitsPerMatrixCleanOrdering G)
    ∧ (∀ {n : ℕ} (G : SimpleGraph (Fin n)),
        IsChordal G → G.cliqueNum ≤ 3 → TrianglesEdgeDisjoint G →
          PatternAdmitsPerMatrixCleanOrdering G) := by
  sorry


theorem prefix_lemma (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (l : List (Fin n)) (S : Finset (Fin n)) (henum : Enumerates l S)
    (j k : Fin n) (hj : j ∉ S) (hk : k ∉ S)
    (hz : schurEntry A S j k = 0)
    (hg : (gameGraph (patternGraph A) l).Adj j k) :
    ∃ v ∈ S, ∃ l' : List (Fin n), Enumerates l' (S.erase v) ∧
      (gameGraph (patternGraph A) l').Adj j v ∧
      (gameGraph (patternGraph A) l').Adj k v := by
  sorry


theorem refill {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (homega : (patternGraph A).cliqueNum ≤ 3)
    (j k u w : Fin n)
    (hjk : j ≠ k) (huj : u ≠ j) (huk : u ≠ k)
    (hwj : w ≠ j) (hwk : w ≠ k) (hwu : w ≠ u)
    (hjkA : (patternGraph A).Adj j k) (hjuA : (patternGraph A).Adj j u)
    (hkuA : (patternGraph A).Adj k u) (hjwA : (patternGraph A).Adj j w)
    (hkwA : (patternGraph A).Adj k w) (hz : Zeroes A ∅ u j k) :
    A u w = 0 ∧ schurEntry A {u} j w = A j w ∧
      schurEntry A {u} j w ≠ 0 ∧
      schurEntry A {u} k w = A k w ∧
      schurEntry A {u} k w ≠ 0 ∧
      schurEntry A (insert w {u}) j k
        = - (A j w * A k w / schurEntry A {u} w w) ∧
      schurEntry A (insert w {u}) j k ≠ 0 := by
  sorry


theorem schur_basic (hA : A.PosDef) (S : Finset (Fin n)) :
    (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val).PosDef ∧
      (schurSet A S).PosDef := by
  sorry


theorem schur_quotient (hA : A.PosDef) (S : Finset (Fin n)) (v : Fin n)
    (hv : v ∉ S) (j k : Fin n) (hj : j ∉ insert v S)
    (hk : k ∉ insert v S) :
    schurEntry A (insert v S) j k = pivotEntry A S v j k := by
  sorry


theorem slot_empty_spoils_of_head (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : List (Fin n)) {j k : Fin n} (hjk : j ≠ k)
    (hadj : (patternGraph A).Adj j k)
    (hhead : σ.head? = some j ∨ σ.head? = some k) :
    (⟨∅, j, k, by simp, by simp, hjk⟩ : Slot n).Spoils A σ := by
  sorry


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
  sorry


theorem stiemke {m p : ℕ} (T : Matrix (Fin m) (Fin p) ℝ) :
    ((∃ t : Fin p → ℝ, (∀ j, 0 < t j) ∧ Matrix.mulVec T t = 0)
        ∧ ¬ ∃ y : Fin m → ℝ, (∀ j, 0 ≤ Matrix.mulVec T.transpose y j)
          ∧ Matrix.mulVec T.transpose y ≠ 0)
      ∨ ((¬ ∃ t : Fin p → ℝ, (∀ j, 0 < t j) ∧ Matrix.mulVec T t = 0)
        ∧ ∃ y : Fin m → ℝ, (∀ j, 0 ≤ Matrix.mulVec T.transpose y j)
          ∧ Matrix.mulVec T.transpose y ≠ 0) := by
  sorry


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
  sorry


theorem triangle_necessary (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (l : List (Fin n)) (S : Finset (Fin n))
    (henum : Enumerates l S) (j k : Fin n) (hj : j ∉ S) (hk : k ∉ S)
    (hz : schurEntry A S j k = 0)
    (hg : (gameGraph (patternGraph A) l).Adj j k) :
    ∃ (v : Fin n), v ∈ S ∧ ∃ (σ : List (Fin n)), IsOrdering σ ∧
      (fillGraph A σ).IsClique ({j, k, v} : Set (Fin n)) := by
  sorry


theorem universal_pivot_refill (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (S : Finset (Fin n)) (v : Fin n)
    (huniv : IsUniversalAt A S v) :
    (∀ j k : Fin n, j ∉ insert v S → k ∉ insert v S → j ≠ k →
        schurEntry A S j k = 0 →
          schurEntry A (insert v S) j k
            = - (schurEntry A S j v * schurEntry A S k v
                / schurEntry A S v v)
              ∧ schurEntry A (insert v S) j k ≠ 0)
      ∧ ∀ j k : Fin n, j ∉ insert v S → k ∉ insert v S → j ≠ k →
          (schurEntry A (insert v S) j k = 0 ↔ Zeroes A S v j k) := by
  sorry


theorem universal_successor (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (S : Finset (Fin n)) (p q : Fin n) (huniv : IsUniversalAt A S p)
    (hq : q ∉ S) (hqp : q ≠ p)
    (hweak : ∀ x : Fin n, x ∉ S → schurEntry A S q x ≠ 0 →
      logMag A S q x ≤ logMag A S p q) :
    IsUniversalAt A (insert p S) q := by
  sorry


theorem zero_leg (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (S : Finset (Fin n)) (j k v : Fin n)
    (hj : j ∉ S) (hk : k ∉ S) (hv : v ∉ S) (_hjk : j ≠ k)
    (hjv : j ≠ v) (hkv : k ≠ v) (hleg : schurEntry A S j v = 0) :
    schurEntry A (insert v S) j k = schurEntry A S j k ∧
      (schurEntry A S j k = 0 ↔ schurEntry A (insert v S) j k = 0) := by
  sorry

end CholeskyCancellations

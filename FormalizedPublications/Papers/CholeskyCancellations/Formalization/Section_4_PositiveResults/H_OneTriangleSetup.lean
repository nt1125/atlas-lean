/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.TakeWhile
import Section_4_PositiveResults.G_ExistsPeelVertex

/-! # One-triangle setup (paper Section 4)

Exactly-one-triangle and edge-disjoint-triangle predicates, index bookkeeping, and the long-path endpoint lemma (`exists_peel_vertex_iii`). Split from `Positives.lean`.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as `Defs.lean`; graph classes are predicates on `SimpleGraph (Fin n)` patterns and cleanliness is quantified per SPD realization through `PatternAdmitsPerMatrixCleanOrdering`. (Plain comment: a docstring cannot precede `variable`.) -/
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



/-- The support index of the `i`-th vertex of a path is `i`. -/
theorem idxOf_getVert_of_isPath {G : SimpleGraph (Fin n)}
    {a b : Fin n} (P : G.Walk a b) (hP : P.IsPath) {i : ℕ}
    (hi : i ≤ P.length) : P.support.idxOf (P.getVert i) = i := by
  classical
  have hmem : P.getVert i ∈ P.support :=
    P.getVert_mem_support i
  exact hP.getVert_injOn
    (Set.mem_Iic.mpr (by
      have h2 := List.idxOf_lt_length_of_mem hmem
      rw [SimpleGraph.Walk.length_support] at h2
      omega))
    (Set.mem_Iic.mpr hi)
    (P.getVert_support_idxOf hmem)



/-- Support index in an appended list, element in the left part. -/
theorem list_idxOf_append_left {l₁ l₂ : List (Fin n)} {z : Fin n}
    (hz : z ∈ l₁) : (l₁ ++ l₂).idxOf z = l₁.idxOf z := by
  induction l₁ with
  | nil => cases hz
  | cons x t ih =>
      by_cases hxz : x = z
      · subst hxz
        rw [List.cons_append, List.idxOf_cons_self,
          List.idxOf_cons_self]
      · have hzt : z ∈ t := List.mem_of_ne_of_mem (Ne.symm hxz) hz
        rw [List.cons_append, List.idxOf_cons, List.idxOf_cons]
        simp only [beq_iff_eq, hxz, ite_false, ih hzt]



/-- Support index in an appended list, element outside the left
part. -/
theorem list_idxOf_append_right {l₁ l₂ : List (Fin n)} {z : Fin n}
    (hz : z ∉ l₁) :
    (l₁ ++ l₂).idxOf z = l₁.length + l₂.idxOf z := by
  induction l₁ with
  | nil => simp
  | cons x t ih =>
      have hxz : x ≠ z := fun h => hz (h ▸ (by simp : x ∈ x :: t))
      have hzt : z ∉ t := fun h => hz (List.mem_cons_of_mem x h)
      rw [List.cons_append, List.idxOf_cons, List.length_cons]
      simp only [beq_iff_eq, hxz, ite_false, ih hzt]
      omega



/-- Subpaths of a path: between two support vertices in support
order there is a subpath, with length the index difference, edges
among the original edges, and support indices in range. -/
theorem exists_subpath {G : SimpleGraph (Fin n)}
    {a b u v : Fin n} (P : G.Walk a b) (hP : P.IsPath)
    (hu : u ∈ P.support) (hv : v ∈ P.support)
    (hord : P.support.idxOf u ≤ P.support.idxOf v) :
    ∃ Q : G.Walk u v, Q.IsPath ∧
      (∀ z ∈ Q.support, z ∈ P.support) ∧ Q.edges ⊆ P.edges ∧
      Q.length = P.support.idxOf v - P.support.idxOf u ∧
      ∀ z ∈ Q.support, P.support.idxOf u ≤ P.support.idxOf z ∧
        P.support.idxOf z ≤ P.support.idxOf v := by
  classical
  have hu_w : u ∈ (P.takeUntil v hv).support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    refine ⟨P.support.idxOf u, ?_, ?_⟩
    · exact (SimpleGraph.Walk.getVert_takeUntil hv
        (show P.support.idxOf u ≤ (P.takeUntil v hv).length by
          rw [P.length_takeUntil hv]; exact hord)).trans
        (P.getVert_support_idxOf hu)
    · rw [P.length_takeUntil hv]; exact hord
  have hgetv : (P.takeUntil v hv).getVert (P.support.idxOf u) = u :=
    (SimpleGraph.Walk.getVert_takeUntil hv
      (show P.support.idxOf u ≤ (P.takeUntil v hv).length by
        rw [P.length_takeUntil hv]; exact hord)).trans
      (P.getVert_support_idxOf hu)
  have hidx_w : (P.takeUntil v hv).support.idxOf u
      = P.support.idxOf u := by
    have h1 : (P.takeUntil v hv).getVert
        ((P.takeUntil v hv).support.idxOf u) = u :=
      (P.takeUntil v hv).getVert_support_idxOf hu_w
    exact (hP.takeUntil hv).getVert_injOn
      (Set.mem_Iic.mpr (by
        have h2 := List.idxOf_lt_length_of_mem hu_w
        rw [SimpleGraph.Walk.length_support] at h2
        omega))
      (Set.mem_Iic.mpr (by
        rw [P.length_takeUntil hv]; exact hord))
      (h1.trans hgetv.symm)
  have hQlen : ((P.takeUntil v hv).dropUntil u hu_w).length
      = P.support.idxOf v - P.support.idxOf u := by
    rw [SimpleGraph.Walk.length_dropUntil, hidx_w,
      P.length_takeUntil hv]
  refine ⟨(P.takeUntil v hv).dropUntil u hu_w,
    (hP.takeUntil hv).dropUntil hu_w, ?_, ?_, hQlen, ?_⟩
  · intro z hz
    exact P.support_takeUntil_subset_support hv
      ((P.takeUntil v hv).support_dropUntil_subset_support hu_w hz)
  · intro e he
    exact P.edges_takeUntil_subset_edges hv
      ((P.takeUntil v hv).edges_dropUntil_subset_edges hu_w he)
  · intro z hz
    have hz_w : z ∈ (P.takeUntil v hv).support :=
      (P.takeUntil v hv).support_dropUntil_subset_support hu_w hz
    obtain ⟨t₁, ht₁⟩ := P.support_takeUntil_prefix_support hv
    obtain ⟨l₂, hl₂⟩ :=
      (P.takeUntil v hv).support_dropUntil_suffix_support hu_w
    have hidxP : P.support.idxOf z
        = (P.takeUntil v hv).support.idxOf z := by
      conv_lhs => rw [← ht₁]
      exact list_idxOf_append_left hz_w
    have hnd : (l₂ ++ ((P.takeUntil v hv).dropUntil u
        hu_w).support).Nodup := by
      rw [hl₂]
      exact (hP.takeUntil hv).support_nodup
    rw [List.nodup_append] at hnd
    have hz_l₂ : z ∉ l₂ := fun hz2 => hnd.2.2 z hz2 z hz rfl
    have hidxW : (P.takeUntil v hv).support.idxOf z
        = l₂.length
          + ((P.takeUntil v hv).dropUntil u hu_w).support.idxOf z := by
      conv_lhs => rw [← hl₂]
      exact list_idxOf_append_right hz_l₂
    have hllen2 : l₂.length = P.support.idxOf u := by
      have h1 := congrArg List.length hl₂
      rw [List.length_append, SimpleGraph.Walk.length_support,
        SimpleGraph.Walk.length_support, hQlen,
        P.length_takeUntil hv] at h1
      omega
    constructor
    · rw [hidxP, hidxW, hllen2]
      exact Nat.le_add_right _ _
    · rw [hidxP]
      have h3 := List.idxOf_lt_length_of_mem hz_w
      rw [SimpleGraph.Walk.length_support, P.length_takeUntil hv]
        at h3
      omega



/-- Consecutive vertices of a path (in support-index order) form an
edge of the path. -/
theorem mem_edges_of_idxOf_succ {G : SimpleGraph (Fin n)}
    {a b x y : Fin n} (Q : G.Walk a b) (hQ : Q.IsPath)
    (hx : x ∈ Q.support) (hy : y ∈ Q.support)
    (h : Q.support.idxOf y = Q.support.idxOf x + 1) :
    s(x, y) ∈ Q.edges := by
  classical
  obtain ⟨W, hW, -, hWedges, hWlen, -⟩ :=
    exists_subpath Q hQ hx hy (by omega)
  have hWlen1 : W.length = 1 := by omega
  have hxy : x ≠ y := by
    intro heq
    subst heq
    omega
  obtain ⟨y', hadj, W', hW'⟩ :=
    exists_cons_of_ne hxy W
  have hlen0 : W'.length = 0 := by
    have h2 := congrArg SimpleGraph.Walk.length hW'
    rw [SimpleGraph.Walk.length_cons] at h2
    omega
  have hy' : y' = y := by
    have h1 : W'.getVert 0 = y' := SimpleGraph.Walk.getVert_zero W'
    have h2 : W'.getVert W'.length = y :=
      SimpleGraph.Walk.getVert_length W'
    rw [hlen0] at h2
    exact h1.symm.trans h2
  have hW'e : W'.edges = [] := by
    have h2 : W'.edges.length = 0 := by
      rw [SimpleGraph.Walk.length_edges]
      exact hlen0
    exact List.length_eq_zero_iff.mp h2
  have hedges : W.edges = [s(x, y)] := by
    rw [hW', SimpleGraph.Walk.edges_cons, hW'e, hy']
  exact hWedges (hedges ▸ List.mem_singleton_self _)



/-- Appending two paths whose supports meet only at the junction
gives a path. -/
theorem isPath_append_of_disjoint {G : SimpleGraph (Fin n)}
    {a b c : Fin n} (P : G.Walk a b) (Q : G.Walk b c)
    (hP : P.IsPath) (hQ : Q.IsPath)
    (hdisj : ∀ z ∈ P.support, ∀ w ∈ Q.support, w ≠ b → z ≠ w) :
    (P.append Q).IsPath := by
  classical
  have hb_tail : b ∉ Q.support.tail := by
    obtain ⟨x, t, ht⟩ := List.exists_cons_of_ne_nil
      (SimpleGraph.Walk.support_ne_nil Q)
    have hx : x = b := by
      have h1 : Q.support.idxOf x = 0 := by
        rw [ht]
        exact List.idxOf_cons_self
      have h2 : Q.support.idxOf b = 0 := by
        have h3 := idxOf_getVert_of_isPath Q hQ (Nat.zero_le _)
        rwa [SimpleGraph.Walk.getVert_zero] at h3
      have h4 := Q.getVert_support_idxOf
        (show x ∈ Q.support by rw [ht]; simp)
      have h5 := Q.getVert_support_idxOf Q.start_mem_support
      rw [h1] at h4
      rw [h2] at h5
      exact h4.symm.trans h5
    have hnd := hQ.support_nodup
    rw [ht, hx, List.nodup_cons] at hnd
    rw [ht, hx, List.tail_cons]
    exact hnd.1
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append, List.nodup_append]
  refine ⟨hP.support_nodup, hQ.support_nodup.tail, ?_⟩
  intro z hz w hw
  exact hdisj z hz w (List.mem_of_mem_tail hw)
    (fun hwb => hb_tail (hwb ▸ hw))



/-- Three pairwise-adjacent vertices form a 3-clique finset. -/
theorem isClique_triple {G : SimpleGraph (Fin n)} {x y z : Fin n}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    G.IsClique (↑({x, y, z} : Finset (Fin n)) : Set (Fin n)) ∧
      ({x, y, z} : Finset (Fin n)).card = 3 := by
  classical
  refine ⟨?_, ?_⟩
  · intro p hp r hr hpr
    rw [Finset.mem_coe] at hp hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hr
    rcases hp with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl
    · exact absurd rfl hpr
    · exact hxy
    · exact hxz
    · exact hxy.symm
    · exact absurd rfl hpr
    · exact hyz
    · exact hxz.symm
    · exact hyz.symm
    · exact absurd rfl hpr
  · rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxy.ne, hxz.ne⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact hyz.ne),
      Finset.card_singleton]



/-- Two distinct triangles cannot share an edge when triangles are
pairwise edge-disjoint. -/
theorem false_of_shared_edge_triangles {G : SimpleGraph (Fin n)}
    (hedge : TrianglesEdgeDisjoint G) {p q r₁ r₂ : Fin n}
    (hpq : G.Adj p q) (hpr₁ : G.Adj p r₁) (hqr₁ : G.Adj q r₁)
    (hpr₂ : G.Adj p r₂) (hqr₂ : G.Adj q r₂) (hne : r₁ ≠ r₂) :
    False := by
  classical
  obtain ⟨hc1, hcard1⟩ := isClique_triple hpq hpr₁ hqr₁
  obtain ⟨hc2, hcard2⟩ := isClique_triple hpq hpr₂ hqr₂
  have hne12 : ({p, q, r₁} : Finset (Fin n)) ≠ {p, q, r₂} := by
    intro heq
    have hmem : r₁ ∈ ({p, q, r₂} : Finset (Fin n)) :=
      heq ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact (Ne.symm hpr₁.ne) h
    · exact (Ne.symm hqr₁.ne) h
    · exact hne h
  have hle := hedge _ _ hcard1 hc1 hcard2 hc2 hne12
  have hsub : ({p, q} : Finset (Fin n))
      ⊆ {p, q, r₁} ∩ {p, q, r₂} := by
    intro z hz
    rw [Finset.mem_inter]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with rfl | rfl
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩
  have h2 : 2 ≤ ({p, q, r₁} ∩ {p, q, r₂} : Finset (Fin n)).card := by
    have h3 := Finset.card_le_card hsub
    rwa [Finset.card_pair hpq.ne] at h3
  omega



/-- **Dirac endpoint step.** The endpoint of a longest path inside
`R` in a chordal graph with pairwise edge-disjoint triangles is
simplicial inside `R`: otherwise two nonadjacent neighbours of the
endpoint joined by a shortest endpoint-avoiding path inside `R`
form a chordless cycle of length at least four (a chord either
shortens the path or creates two triangles sharing an edge),
contradicting chordality. -/
theorem simplicial_of_longest_path_endpoint {G : SimpleGraph (Fin n)}
    (hG : IsChordal G) (hedge : TrianglesEdgeDisjoint G)
    {R : Finset (Fin n)} {a b : Fin n}
    (P : G.Walk a b) (hP : P.IsPath)
    (hPR : ∀ z ∈ P.support, z ∈ R)
    (hmax : ∀ (a' b' : Fin n) (q : G.Walk a' b'), q.IsPath →
      (∀ z ∈ q.support, z ∈ R) → q.length ≤ P.length) :
    ∀ u v : Fin n, u ∈ R → v ∈ R → G.Adj b u → G.Adj b v →
      u = v ∨ G.Adj u v := by
  classical
  intro u₀ v₀ hu₀ hv₀ hbu₀ hbv₀
  by_cases h1 : u₀ = v₀
  · exact Or.inl h1
  by_cases h2 : G.Adj u₀ v₀
  · exact Or.inr h2
  exfalso
  have hmem : ∀ x ∈ R, G.Adj b x → x ∈ P.support :=
    maximal_endpoint_mem P hP hPR
      (fun b' q' hq' hqR' => hmax a b' q' hq' hqR')
  have hu0P : u₀ ∈ P.support := hmem u₀ hu₀ hbu₀
  have hv0P : v₀ ∈ P.support := hmem v₀ hv₀ hbv₀
  have hidxb : P.support.idxOf b = P.length := by
    have h3 := idxOf_getVert_of_isPath P hP le_rfl
    rwa [SimpleGraph.Walk.getVert_length] at h3
  have hidxlt : ∀ x ∈ P.support, x ≠ b →
      P.support.idxOf x < P.length := by
    intro x hx hxb
    have h3 := List.idxOf_lt_length_of_mem hx
    rw [SimpleGraph.Walk.length_support] at h3
    by_contra hcon
    push Not at hcon
    have heq : P.support.idxOf x = P.length := by omega
    have h4 := P.getVert_support_idxOf hx
    rw [heq, SimpleGraph.Walk.getVert_length] at h4
    exact hxb h4.symm
  have hexpath : ∃ Q₀ : G.Walk u₀ v₀, Q₀.IsPath ∧
      (∀ z ∈ Q₀.support, z ∈ R) ∧ b ∉ Q₀.support := by
    rcases le_total (P.support.idxOf u₀) (P.support.idxOf v₀) with
      hord | hord
    · obtain ⟨Q₀, hQ₀, hsupp, -, -, hrange⟩ :=
        exists_subpath P hP hu0P hv0P hord
      refine ⟨Q₀, hQ₀, fun z hz => hPR z (hsupp z hz), ?_⟩
      intro hbmem
      have h5 := (hrange b hbmem).2
      rw [hidxb] at h5
      have h6 := hidxlt v₀ hv0P (Ne.symm hbv₀.ne)
      omega
    · obtain ⟨Q₀, hQ₀, hsupp, -, -, hrange⟩ :=
        exists_subpath P hP hv0P hu0P hord
      have hbrev : b ∉ Q₀.reverse.support := by
        intro hbmem
        rw [SimpleGraph.Walk.support_reverse,
          List.mem_reverse] at hbmem
        have h5 := (hrange b hbmem).2
        rw [hidxb] at h5
        have h6 := hidxlt u₀ hu0P (Ne.symm hbu₀.ne)
        omega
      exact ⟨Q₀.reverse,
        SimpleGraph.Walk.IsPath.mk' (by
          rw [SimpleGraph.Walk.support_reverse]
          exact List.nodup_reverse.mpr hQ₀.support_nodup),
        fun z hz => by
          rw [SimpleGraph.Walk.support_reverse,
            List.mem_reverse] at hz
          exact hPR z (hsupp z hz), hbrev⟩
  obtain ⟨Q₀, hQ₀, hQ₀R, hbQ₀⟩ := hexpath
  set Pcnt : ℕ → Prop := fun L => ∃ (u' v' : Fin n)
    (Q' : G.Walk u' v'), u' ∈ R ∧ v' ∈ R ∧ u' ≠ v' ∧
      G.Adj b u' ∧ G.Adj b v' ∧ ¬ G.Adj u' v' ∧ Q'.IsPath ∧
      (∀ z ∈ Q'.support, z ∈ R) ∧ b ∉ Q'.support ∧
      Q'.length = L with hPdef
  have hPex : ∃ L, Pcnt L := ⟨Q₀.length, u₀, v₀, Q₀, hu₀, hv₀, h1,
    hbu₀, hbv₀, h2, hQ₀, hQ₀R, hbQ₀, rfl⟩
  obtain ⟨u, v, Q, hu, hv, huv, hbu, hbv, hnuv, hQ, hQR, hbQ,
    hlenQ⟩ := Nat.find_spec hPex
  have hmin : ∀ (u' v' : Fin n) (Q' : G.Walk u' v'), u' ∈ R →
      v' ∈ R → u' ≠ v' → G.Adj b u' → G.Adj b v' → ¬ G.Adj u' v' →
      Q'.IsPath → (∀ z ∈ Q'.support, z ∈ R) → b ∉ Q'.support →
      Q.length ≤ Q'.length := by
    intro u' v' Q' h1' h2' h3' h4' h5' h6' h7' h8' h9'
    have hle := Nat.find_min' hPex (show Pcnt Q'.length from
      ⟨u', v', Q', h1', h2', h3', h4', h5', h6', h7', h8', h9', rfl⟩)
    omega
  have hQlen2 : 2 ≤ Q.length := by
    have hne0 : Q.length ≠ 0 := by
      intro h0
      have h3 : Q.getVert 0 = u := SimpleGraph.Walk.getVert_zero Q
      have h4 : Q.getVert Q.length = v :=
        SimpleGraph.Walk.getVert_length Q
      rw [h0] at h4
      exact huv (h3.symm.trans h4)
    have hne1 : Q.length ≠ 1 := by
      intro h01
      have h3 := Q.adj_getVert_succ (show 0 < Q.length by omega)
      rw [show Q.getVert (0 + 1) = v from by
        rw [show (0 + 1 : ℕ) = Q.length by omega]
        exact SimpleGraph.Walk.getVert_length Q,
        SimpleGraph.Walk.getVert_zero] at h3
      exact hnuv h3
    omega
  set C := (Q.append (SimpleGraph.Walk.cons hbv.symm
      SimpleGraph.Walk.nil)).append
    (SimpleGraph.Walk.cons hbu SimpleGraph.Walk.nil) with hCdef
  have hcyc : C.IsCycle :=
    isCycle_append_two_edges Q hQ hbv.symm hbu hbQ (Ne.symm huv)
      (Ne.symm hbu.ne) (by omega)
  have hCsupp : C.support = Q.support ++ [b, u] := by
    rw [hCdef, SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_append]
    simp [SimpleGraph.Walk.support_cons]
  have hCedges : C.edges = Q.edges ++ [s(v, b), s(b, u)] := by
    rw [hCdef, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_nil, SimpleGraph.Walk.edges_nil]
    simp
  have hClen : C.length = Q.length + 2 := by
    rw [hCdef, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_nil, SimpleGraph.Walk.length_nil]
  have hidx_u : Q.support.idxOf u = 0 := by
    have h3 := idxOf_getVert_of_isPath Q hQ (Nat.zero_le _)
    rwa [SimpleGraph.Walk.getVert_zero] at h3
  have hidx_v : Q.support.idxOf v = Q.length := by
    have h3 := idxOf_getVert_of_isPath Q hQ le_rfl
    rwa [SimpleGraph.Walk.getVert_length] at h3
  have hidx_lt : ∀ z ∈ Q.support, Q.support.idxOf z ≤ Q.length := by
    intro z hz
    have h3 := List.idxOf_lt_length_of_mem hz
    rw [SimpleGraph.Walk.length_support] at h3
    omega
  have hidx_inj : ∀ z ∈ Q.support, ∀ w ∈ Q.support,
      Q.support.idxOf z = Q.support.idxOf w → z = w := by
    intro z hz w hw heq
    have h3 := Q.getVert_support_idxOf hz
    have h4 := Q.getVert_support_idxOf hw
    rw [heq] at h3
    exact h3.symm.trans h4
  have hbcase : ∀ y ∈ Q.support, G.Adj b y → s(b, y) ∈ C.edges := by
    intro y hy hadjby
    by_contra he
    have hyR : y ∈ R := hQR y hy
    have hyu : y ≠ u := by
      intro h
      apply he
      rw [hCedges, h]
      simp
    have hyv : y ≠ v := by
      intro h
      apply he
      rw [hCedges, h, Sym2.eq_swap]
      simp
    have hiy1 : 0 < Q.support.idxOf y := by
      by_contra hcon
      push Not at hcon
      have heq0 : Q.support.idxOf y = 0 := by omega
      exact hyu (hidx_inj y hy u Q.start_mem_support
        (by rw [heq0, hidx_u]))
    have hiy2 : Q.support.idxOf y < Q.length := by
      by_contra hcon
      push Not at hcon
      have heqL : Q.support.idxOf y = Q.length := by
        have h3 := hidx_lt y hy
        omega
      exact hyv (hidx_inj y hy v Q.end_mem_support
        (by rw [heqL, hidx_v]))
    have hadjuy : G.Adj u y := by
      by_contra hcon
      obtain ⟨Q₁, hQ₁, hsupp, -, hlen, -⟩ :=
        exists_subpath Q hQ Q.start_mem_support hy
          (by rw [hidx_u]; exact Nat.zero_le _)
      have h4 := hmin u y Q₁ hu hyR (Ne.symm hyu) hbu hadjby hcon
        hQ₁ (fun z hz => hQR z (hsupp z hz))
        (fun hz => hbQ (hsupp b hz))
      rw [hidx_u, Nat.sub_zero] at hlen
      omega
    have hadjyv : G.Adj y v := by
      by_contra hcon
      obtain ⟨Q₂, hQ₂, hsupp, -, hlen, -⟩ :=
        exists_subpath Q hQ hy Q.end_mem_support
          (by rw [hidx_v]; exact hidx_lt y hy)
      have h4 := hmin y v Q₂ hyR hv hyv hadjby hbv hcon hQ₂
        (fun z hz => hQR z (hsupp z hz))
        (fun hz => hbQ (hsupp b hz))
      rw [hidx_v] at hlen
      omega
    exact false_of_shared_edge_triangles hedge hadjby hbu
      hadjuy.symm hbv hadjyv huv
  have shortcut : ∀ (x y : Fin n) (hxQ : x ∈ Q.support)
      (hyQ : y ∈ Q.support), G.Adj x y →
      Q.support.idxOf x + 1 < Q.support.idxOf y → False := by
    intro x y hxQ hyQ hadj hlt2
    obtain ⟨Q₁, hQ₁, hs1, -, hl1, hr1⟩ :=
      exists_subpath Q hQ Q.start_mem_support hxQ
        (by rw [hidx_u]; exact Nat.zero_le _)
    obtain ⟨Q₂, hQ₂, hs2, -, hl2, hr2⟩ :=
      exists_subpath Q hQ hyQ Q.end_mem_support
        (by rw [hidx_v]; exact hidx_lt y hyQ)
    rw [hidx_u, Nat.sub_zero] at hl1
    rw [hidx_v] at hl2
    set Q' := (Q₁.append (SimpleGraph.Walk.cons hadj
        SimpleGraph.Walk.nil)).append Q₂ with hQ'def
    have hiy : Q.support.idxOf y ≤ Q.length := hidx_lt y hyQ
    have hlen' : Q'.length < Q.length := by
      rw [hQ'def, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_nil, hl1, hl2]
      omega
    have hQ1e : (Q₁.append (SimpleGraph.Walk.cons hadj
        SimpleGraph.Walk.nil)).support = Q₁.support ++ [y] := by
      rw [SimpleGraph.Walk.support_append]
      simp [SimpleGraph.Walk.support_cons]
    have hpath1 : (Q₁.append (SimpleGraph.Walk.cons hadj
        SimpleGraph.Walk.nil)).IsPath := by
      apply isPath_append_of_disjoint Q₁ _ hQ₁
        (SimpleGraph.Walk.IsPath.mk' (by
          rw [SimpleGraph.Walk.support_cons]
          exact List.nodup_cons.mpr
            ⟨by simp [hadj.ne], by simp⟩))
      intro z hz w hw hwx
      have hwy : w = y := by
        rw [SimpleGraph.Walk.support_cons] at hw
        simp only [SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hw
        rcases hw with h | h
        · exact absurd h hwx
        · exact h
      intro hzw
      have h4 := (hr1 z hz).2
      have h5 : Q.support.idxOf z = Q.support.idxOf y := by
        rw [hzw, hwy]
      omega
    have hpath' : Q'.IsPath := by
      rw [hQ'def]
      apply isPath_append_of_disjoint _ Q₂ hpath1 hQ₂
      intro z hz w hw hwy
      rw [hQ1e] at hz
      have hwidx : Q.support.idxOf y ≤ Q.support.idxOf w :=
        (hr2 w hw).1
      have hzidx : Q.support.idxOf z ≤ Q.support.idxOf x ∨
          z = y := by
        rcases List.mem_append.mp hz with h | h
        · exact Or.inl (hr1 z h).2
        · exact Or.inr (by simpa using h)
      intro hzw
      rcases hzidx with hle | rfl
      · have h5 : Q.support.idxOf z = Q.support.idxOf w := by
          rw [hzw]
        omega
      · exact hwy hzw.symm
    have hQR' : ∀ z ∈ Q'.support, z ∈ R := by
      intro z hz
      rw [hQ'def, SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with (h | h) | h
      · exact hQR z (hs1 z h)
      · rw [SimpleGraph.Walk.support_cons] at h
        simp only [SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact hQR z hxQ
        · exact hQR z hyQ
      · exact hQR z (hs2 z h)
    have hbQ' : b ∉ Q'.support := by
      intro hz
      rw [hQ'def, SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with (h | h) | h
      · exact hbQ (hs1 b h)
      · rw [SimpleGraph.Walk.support_cons] at h
        simp only [SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact hbQ hxQ
        · exact hbQ hyQ
      · exact hbQ (hs2 b h)
    have h4 := hmin u v Q' hu hv huv hbu hbv hnuv hpath' hQR' hbQ'
    omega
  have hchord : ∀ x ∈ C.support, ∀ y ∈ C.support, G.Adj x y →
      s(x, y) ∈ C.edges := by
    intro x hx y hy hadjxy
    have hxcase : x ∈ Q.support ∨ x = b := by
      rw [hCsupp] at hx
      rcases List.mem_append.mp hx with h | h
      · exact Or.inl h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl Q.start_mem_support
    have hycase : y ∈ Q.support ∨ y = b := by
      rw [hCsupp] at hy
      rcases List.mem_append.mp hy with h | h
      · exact Or.inl h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl Q.start_mem_support
    rcases hxcase with hxQ | rfl
    · rcases hycase with hyQ | rfl
      · by_contra he
        have hxy : x ≠ y := hadjxy.ne
        have hidxne : Q.support.idxOf x ≠ Q.support.idxOf y :=
          fun h => hxy (hidx_inj x hxQ y hyQ h)
        rcases lt_or_gt_of_ne hidxne with hlt | hgt
        · by_cases hsucc :
            Q.support.idxOf y = Q.support.idxOf x + 1
          · have h3 := mem_edges_of_idxOf_succ Q hQ hxQ hyQ hsucc
            exact he (by
              rw [hCedges]
              exact List.mem_append_left _ h3)
          · exact shortcut x y hxQ hyQ hadjxy (by omega)
        · by_cases hsucc :
            Q.support.idxOf x = Q.support.idxOf y + 1
          · have h3 := mem_edges_of_idxOf_succ Q hQ hyQ hxQ hsucc
            rw [Sym2.eq_swap] at h3
            exact he (by
              rw [hCedges]
              exact List.mem_append_left _ h3)
          · exact shortcut y x hyQ hxQ hadjxy.symm (by omega)
      · have h3 := hbcase x hxQ hadjxy.symm
        rwa [Sym2.eq_swap] at h3
    · rcases hycase with hyQ | rfl
      · exact hbcase y hyQ hadjxy
      · exact absurd rfl hadjxy.ne
  set s : Finset (Fin n) := C.support.toFinset with hsdef
  have hw : ∀ x ∈ C.support, x ∈ (↑s : Set (Fin n)) := by
    intro x hx
    rw [hsdef]
    exact List.mem_toFinset.mpr hx
  obtain ⟨hci, hleni⟩ := isCycle_induce C hcyc hw
  have hL : (C.induce (↑s) hw).length < 4 := by
    refine hG s _ _ hci ?_ ?_
    · intro e he
      obtain ⟨a, b', hab⟩ : ∃ a b', s(a, b') = e :=
        (Sym2.exists (f := fun z => z = e)).mp ⟨e, rfl⟩
      subst hab
      have hadj : (G.induce (↑s : Set (Fin n))).Adj a b' :=
        (SimpleGraph.mem_edgeSet _).mp he
      rw [SimpleGraph.induce_adj] at hadj
      have ha : a.val ∈ C.support :=
        List.mem_toFinset.mp (hsdef ▸ Finset.mem_coe.mp a.2)
      have hb' : b'.val ∈ C.support :=
        List.mem_toFinset.mp (hsdef ▸ Finset.mem_coe.mp b'.2)
      exact (mem_edges_induce C hw).mpr
        (hchord a.val ha b'.val hb' hadj)
    · intro z hz
      have hzsup : z ∈ C.support :=
        List.mem_toFinset.mp (hsdef ▸ Finset.mem_coe.mp hz)
      have hmap : (C.induce (↑s) hw).support.map Subtype.val
          = C.support := by
        rw [SimpleGraph.Walk.support_induce]
        simp
      have h2 : z ∈ (C.induce (↑s) hw).support.map Subtype.val :=
        hmap ▸ hzsup
      rw [List.mem_map] at h2
      obtain ⟨a, ha, haz⟩ := h2
      exact ⟨a, ha, haz⟩
  rw [hleni, hClen] at hL
  omega



/-- **Peel vertex existence (edge-disjoint triangles case).** In a
chordal graph with `ω ≤ 3` and pairwise edge-disjoint triangles,
every nonempty survivor set `R` contains either a vertex with at
most one neighbour in `R`, or a leaf triangle: a triangle
`{c, a, b} ⊆ R` whose vertices `a, b` have no `R`-neighbours
outside the triangle. Proof: the endpoint `b₀` of a longest path
in `R` is simplicial (`simplicial_of_longest_path_endpoint`), so it
has at most two neighbours in `R` (a third would make a
4-clique). If at most one, done. If exactly two, apply the
induction hypothesis to `R \ {b₀}`: a pendant vertex there either
stays pendant in `R` or is one of the two neighbours, making a
leaf triangle with `b₀`; a leaf triangle there cannot use either
neighbour of `b₀` as a leaf vertex (that would create two
triangles sharing the edge between the neighbours), so it lifts
to `R`. This replaces the paper's block-cut tree argument in the
proof of Theorem 4.8 (iii). -/
theorem exists_peel_vertex_iii {G : SimpleGraph (Fin n)}
    (hG : IsChordal G) (hω : G.cliqueNum ≤ 3)
    (hedge : TrianglesEdgeDisjoint G) :
    ∀ (R : Finset (Fin n)), R.Nonempty →
      (∃ x ∈ R, ∃ u : Fin n, ∀ y : Fin n, y ∈ R → y ≠ x →
        G.Adj x y → y = u) ∨
      (∃ c a b : Fin n, c ∈ R ∧ a ∈ R ∧ b ∈ R ∧ c ≠ a ∧ c ≠ b ∧
        a ≠ b ∧ G.Adj c a ∧ G.Adj c b ∧ G.Adj a b ∧
        (∀ y : Fin n, y ∈ R → y ≠ a → G.Adj a y → y = c ∨ y = b) ∧
        (∀ y : Fin n, y ∈ R → y ≠ b → G.Adj b y → y = c ∨ y = a)) := by
  classical
  have key : ∀ (m : ℕ) (R : Finset (Fin n)), R.card = m →
      R.Nonempty →
      (∃ x ∈ R, ∃ u : Fin n, ∀ y : Fin n, y ∈ R → y ≠ x →
        G.Adj x y → y = u) ∨
      (∃ c a b : Fin n, c ∈ R ∧ a ∈ R ∧ b ∈ R ∧ c ≠ a ∧ c ≠ b ∧
        a ≠ b ∧ G.Adj c a ∧ G.Adj c b ∧ G.Adj a b ∧
        (∀ y : Fin n, y ∈ R → y ≠ a → G.Adj a y → y = c ∨ y = b) ∧
        (∀ y : Fin n, y ∈ R → y ≠ b → G.Adj b y → y = c ∨ y = a)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
        intro R hcard hne
        obtain ⟨a₀, b, P, hP, hPR, hmax⟩ :=
          exists_longest_path_in (G := G) hne
        have hbR : b ∈ R := hPR b P.end_mem_support
        have hsimp : ∀ u v : Fin n, u ∈ R → v ∈ R → G.Adj b u →
            G.Adj b v → u = v ∨ G.Adj u v :=
          simplicial_of_longest_path_endpoint hG hedge P hP hPR hmax
        set N := R.filter (fun y => G.Adj b y) with hNdef
        have hNmem : ∀ y : Fin n, y ∈ N ↔ y ∈ R ∧ G.Adj b y := by
          intro y
          simp [hNdef]
        have hcardN : N.card ≤ 2 := by
          have hclq : G.IsClique (↑(insert b N) : Set (Fin n)) := by
            intro p hp r hr hpr
            rw [Finset.mem_coe, Finset.mem_insert] at hp hr
            rcases hp with rfl | hpN
            · rcases hr with rfl | hrN
              · exact absurd rfl hpr
              · exact ((hNmem r).mp hrN).2
            · rcases hr with rfl | hrN
              · exact ((hNmem p).mp hpN).2.symm
              · obtain ⟨hpR, hpb⟩ := (hNmem p).mp hpN
                obtain ⟨hrR, hrb⟩ := (hNmem r).mp hrN
                rcases hsimp p r hpR hrR hpb hrb with h | h
                · exact absurd h hpr
                · exact h
          have hbN : b ∉ N :=
            fun h => ((hNmem b).mp h).2.ne rfl
          have h3 := SimpleGraph.IsClique.card_le_cliqueNum hclq
          rw [Finset.card_insert_of_notMem hbN] at h3
          omega
        by_cases hdeg : N.card ≤ 1
        · left
          by_cases hex : ∃ y : Fin n, y ∈ R ∧ G.Adj b y
          · obtain ⟨y₀, hy₀R, hy₀adj⟩ := hex
            refine ⟨b, hbR, y₀, ?_⟩
            intro y hyR hyb hadj
            exact Finset.card_le_one.mp hdeg y
              ((hNmem y).mpr ⟨hyR, hadj⟩) y₀
              ((hNmem y₀).mpr ⟨hy₀R, hy₀adj⟩)
          · refine ⟨b, hbR, b, ?_⟩
            intro y hyR hyb hadj
            exact absurd ⟨y, hyR, hadj⟩ hex
        · have hcard2 : N.card = 2 := by omega
          obtain ⟨u, v, huv, hNe⟩ := Finset.card_eq_two.mp hcard2
          have huN : u ∈ N := by rw [hNe]; simp
          have hvN : v ∈ N := by rw [hNe]; simp
          obtain ⟨huR, hbu⟩ := (hNmem u).mp huN
          obtain ⟨hvR, hbv⟩ := (hNmem v).mp hvN
          have hadjuv : G.Adj u v := by
            rcases hsimp u v huR hvR hbu hbv with h | h
            · exact absurd h huv
            · exact h
          have hbds : ∀ y : Fin n, y ∈ R → G.Adj b y →
              y = u ∨ y = v := by
            intro y hyR hadj
            have hyN : y ∈ N := (hNmem y).mpr ⟨hyR, hadj⟩
            rw [hNe] at hyN
            simpa only [Finset.mem_insert,
              Finset.mem_singleton] using hyN
          have hcommon : ∀ z : Fin n, z ≠ b → G.Adj z u →
              G.Adj z v → False := by
            intro z hzb hzu hzv
            exact false_of_shared_edge_triangles hedge hadjuv
              hbu.symm hbv.symm hzu.symm hzv.symm (Ne.symm hzb)
          have hcardlt : (R.erase b).card < m := by
            have hpos : 0 < R.card := Finset.card_pos.mpr hne
            rw [Finset.card_erase_of_mem hbR, hcard]
            omega
          have hne' : (R.erase b).Nonempty :=
            ⟨u, Finset.mem_erase.mpr ⟨Ne.symm hbu.ne, huR⟩⟩
          rcases ih (R.erase b).card hcardlt (R.erase b) rfl hne'
            with hA | hB
          · obtain ⟨x, hxR', w, hw⟩ := hA
            have hxR : x ∈ R := Finset.mem_of_mem_erase hxR'
            by_cases hxadj : G.Adj x b
            · have hxuv : x = u ∨ x = v := hbds x hxR hxadj.symm
              rcases hxuv with rfl | rfl
              · have hw' : v = w :=
                  hw v (Finset.mem_erase.mpr
                    ⟨Ne.symm hbv.ne, hvR⟩) (Ne.symm huv) hadjuv
                subst hw'
                right
                refine ⟨v, b, x, hvR, hbR, huR, Ne.symm hbv.ne,
                  Ne.symm huv, hbu.ne, hbv.symm, hadjuv.symm, hbu,
                  ?_, ?_⟩
                · intro y hyR hyb hadj
                  rcases hbds y hyR hadj with h | h
                  · exact Or.inr h
                  · exact Or.inl h
                · intro y hyR hyu hadj
                  by_cases hyb : y = b
                  · exact Or.inr hyb
                  · exact Or.inl (hw y
                      (Finset.mem_erase.mpr ⟨hyb, hyR⟩) hyu hadj)
              · have hw' : u = w :=
                  hw u (Finset.mem_erase.mpr
                    ⟨Ne.symm hbu.ne, huR⟩) huv hadjuv.symm
                subst hw'
                right
                refine ⟨u, b, x, huR, hbR, hvR, Ne.symm hbu.ne,
                  huv, hbv.ne, hbu.symm, hadjuv, hbv, ?_, ?_⟩
                · intro y hyR hyb hadj
                  rcases hbds y hyR hadj with h | h
                  · exact Or.inl h
                  · exact Or.inr h
                · intro y hyR hyv hadj
                  by_cases hyb : y = b
                  · exact Or.inr hyb
                  · exact Or.inl (hw y
                      (Finset.mem_erase.mpr ⟨hyb, hyR⟩) hyv hadj)
            · left
              refine ⟨x, hxR, w, ?_⟩
              intro y hyR hyx hadj
              by_cases hyb : y = b
              · subst hyb
                exact absurd hadj hxadj
              · exact hw y (Finset.mem_erase.mpr ⟨hyb, hyR⟩) hyx
                  hadj
          · obtain ⟨c, a, d, hcR', haR', hdR', hca, hcd, had,
              hcad, hcbd, hadj, ha_bd, hd_bd⟩ := hB
            have hcR : c ∈ R := Finset.mem_of_mem_erase hcR'
            have haR : a ∈ R := Finset.mem_of_mem_erase haR'
            have hdR : d ∈ R := Finset.mem_of_mem_erase hdR'
            have hcb : c ≠ b := (Finset.mem_erase.mp hcR').1
            have hab2 : a ≠ b := (Finset.mem_erase.mp haR').1
            have hdb : d ≠ b := (Finset.mem_erase.mp hdR').1
            have ha_not : a ∉ ({u, v} : Finset (Fin n)) := by
              simp only [Finset.mem_insert, Finset.mem_singleton,
                not_or]
              constructor
              · intro ha₁
                subst ha₁
                rcases ha_bd v (Finset.mem_erase.mpr
                    ⟨Ne.symm hbv.ne, hvR⟩) (Ne.symm huv) hadjuv
                  with h | h
                · exact hcommon d hdb hadj.symm
                    (by rw [h]; exact hcbd.symm)
                · exact hcommon c hcb hcad
                    (by rw [h]; exact hcbd)
              · intro ha₁
                subst ha₁
                rcases ha_bd u (Finset.mem_erase.mpr
                    ⟨Ne.symm hbu.ne, huR⟩) huv hadjuv.symm
                  with h | h
                · exact hcommon d hdb
                    (by rw [h]; exact hcbd.symm) hadj.symm
                · exact hcommon c hcb
                    (by rw [h]; exact hcbd) hcad
            have hd_not : d ∉ ({u, v} : Finset (Fin n)) := by
              simp only [Finset.mem_insert, Finset.mem_singleton,
                not_or]
              constructor
              · intro hd₁
                subst hd₁
                rcases hd_bd v (Finset.mem_erase.mpr
                    ⟨Ne.symm hbv.ne, hvR⟩) (Ne.symm huv) hadjuv
                  with h | h
                · exact hcommon a hab2 hadj
                    (by rw [h]; exact hcad.symm)
                · exact hcommon c hcb hcbd
                    (by rw [h]; exact hcad)
              · intro hd₁
                subst hd₁
                rcases hd_bd u (Finset.mem_erase.mpr
                    ⟨Ne.symm hbu.ne, huR⟩) huv hadjuv.symm
                  with h | h
                · exact hcommon a hab2
                    (by rw [h]; exact hcad.symm) hadj
                · exact hcommon c hcb
                    (by rw [h]; exact hcad) hcbd
            right
            refine ⟨c, a, d, hcR, haR, hdR, hca, hcd, had, hcad,
              hcbd, hadj, ?_, ?_⟩
            · intro y hyR hya hadjy
              by_cases hyb : y = b
              · subst hyb
                have h3 : a = u ∨ a = v := hbds a haR hadjy.symm
                exact absurd (by
                  simp only [Finset.mem_insert,
                    Finset.mem_singleton]
                  exact h3) ha_not
              · exact ha_bd y (Finset.mem_erase.mpr ⟨hyb, hyR⟩)
                  hya hadjy
            · intro y hyR hyd hadjy
              by_cases hyb : y = b
              · subst hyb
                have h3 : d = u ∨ d = v := hbds d hdR hadjy.symm
                exact absurd (by
                  simp only [Finset.mem_insert,
                    Finset.mem_singleton]
                  exact h3) hd_not
              · exact hd_bd y (Finset.mem_erase.mpr ⟨hyb, hyR⟩)
                  hyd hadjy
  intro R hne
  exact key R.card R rfl hne

end CholeskyCancellations

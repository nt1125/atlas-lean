/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.TakeWhile
import Section_4_PositiveResults.E_FanContinuation

/-! # Peeling, cycles, and paths (paper Section 4)

Peeling a vertex with at most one survivor neighbour; cycle/path infrastructure (splitting cycles, induced cycles, cycle support) and longest paths, consumed by the chordal cases of Theorem 4.8 (ii)–(iii).
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as the Section 2 files; graph classes are predicates on `SimpleGraph (Fin n)` patterns and cleanliness is quantified per SPD realization through `PatternAdmitsPerMatrixCleanOrdering`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}



/-- A survivor whose only possible game neighbour among survivors
is `u` has zero legs to every other survivor. -/
theorem schurEntry_eq_zero_of_neighbor_subset {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef)
    {lS : List (Fin n)} {S : Finset (Fin n)}
    (henum : Enumerates lS S) {v u : Fin n}
    (hN : ∀ x : Fin n, x ∉ S → x ≠ v →
      (gameGraph (patternGraph A) lS).Adj v x → x = u)
    {z : Fin n} (hzS : z ∉ S) (hzv : z ≠ v) (hzu : z ≠ u) :
    schurEntry A S z v = 0 := by
  refine schurEntry_eq_zero_of_not_gameAdj hA lS S henum hzv ?_
  intro hAdj
  exact hzu (hN z hzS hzv hAdj.symm)



/-- Peeling a vertex with at most one survivor neighbour: the pivot
is clean (given its single entry), and neither the game graph nor
any off-diagonal survivor entry changes. This is the peeling step
consumed by the chordal cases of paper Theorem 4.8 (ii)–(iii),
where the peeled vertex is pendant in the current graph. -/
theorem peel_singleton_neighbor {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {lS : List (Fin n)}
    {S : Finset (Fin n)} (henum : Enumerates lS S) {v u : Fin n}
    (hv : v ∉ S)
    (hN : ∀ x : Fin n, x ∉ S → x ≠ v →
      (gameGraph (patternGraph A) lS).Adj v x → x = u)
    (hentry : schurEntry A S v u ≠ 0) :
    (∀ x : Fin n, x ∉ S → x ≠ v →
      (gameGraph (patternGraph A) lS).Adj v x →
      schurEntry A S v x ≠ 0)
    ∧ (∀ x y : Fin n, x ∉ insert v S → y ∉ insert v S → x ≠ y →
        schurEntry A (insert v S) x y = schurEntry A S x y)
    ∧ (∀ x y : Fin n, x ∉ insert v S → y ∉ insert v S → x ≠ y →
        ((gameGraph (patternGraph A) (lS ++ [v])).Adj x y
          ↔ (gameGraph (patternGraph A) lS).Adj x y)) := by
  have hleg : ∀ z : Fin n, z ∉ insert v S → z ≠ u →
      schurEntry A S z v = 0 := by
    intro z hz hzu
    have hzS : z ∉ S := fun h => hz (Finset.mem_insert_of_mem h)
    have hzv : z ≠ v :=
      fun hh => hz (hh ▸ Finset.mem_insert_self v S)
    exact schurEntry_eq_zero_of_neighbor_subset hA henum hN hzS hzv
      hzu
  refine ⟨?_, ?_, ?_⟩
  · intro x hxS hxv hAdj
    have hxu : x = u := hN x hxS hxv hAdj
    rw [hxu]
    exact hentry
  · intro x y hx hy hxy
    apply schurEntry_insert_eq_of_leg_zero hA S hv hx hy
    by_cases hxu : x = u
    · exact Or.inr (hleg y hy (fun hh => hxy (hxu.trans hh.symm)))
    · exact Or.inl (hleg x hx hxu)
  · intro x y hx hy hxy
    have hxS : x ∉ S := fun h => hx (Finset.mem_insert_of_mem h)
    have hyS : y ∉ S := fun h => hy (Finset.mem_insert_of_mem h)
    have hxv : x ≠ v :=
      fun hh => hx (hh ▸ Finset.mem_insert_self v S)
    have hyv : y ≠ v :=
      fun hh => hy (hh ▸ Finset.mem_insert_self v S)
    rw [gameGraph_append_singleton, elimStep_adj_iff_of_ne hxy]
    constructor
    · rintro (h | ⟨hxA, hyA⟩)
      · exact h
      · have h1 : x = u := hN x hxS hxv hxA.symm
        have h2 : y = u := hN y hyS hyv hyA.symm
        exact absurd (h1.trans h2.symm) hxy
    · intro h
      exact Or.inl h



/-- Peeling a clean simplicial vertex with exactly the two survivor
neighbours `x₀, y₀` (already adjacent): the pivot is clean given
its two entries and that the `(x₀, y₀)` entry survives it, and no
other entry or game edge changes. -/
theorem peel_clean_simplicial_pair {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef)
    {lS : List (Fin n)} {S : Finset (Fin n)}
    (henum : Enumerates lS S) {v x₀ y₀ : Fin n}
    (hv : v ∉ S) (hx₀ : x₀ ∉ S) (hy₀ : y₀ ∉ S)
    (hvx : v ≠ x₀) (hvy : v ≠ y₀) (hxy : x₀ ≠ y₀)
    (hN : ∀ x : Fin n, x ∉ S → x ≠ v →
      (gameGraph (patternGraph A) lS).Adj v x → x = x₀ ∨ x = y₀)
    (hadj : (gameGraph (patternGraph A) lS).Adj x₀ y₀)
    (hex : schurEntry A S v x₀ ≠ 0) (hey : schurEntry A S v y₀ ≠ 0)
    (hafter : schurEntry A (insert v S) x₀ y₀ ≠ 0) :
    (∀ x : Fin n, x ∉ S → x ≠ v →
      (gameGraph (patternGraph A) lS).Adj v x →
      schurEntry A S v x ≠ 0)
    ∧ (∀ x y : Fin n, x ∉ insert v S → y ∉ insert v S → x ≠ y →
        ¬ SamePair x y x₀ y₀ →
        schurEntry A (insert v S) x y = schurEntry A S x y)
    ∧ (∀ x y : Fin n, x ∉ insert v S → y ∉ insert v S → x ≠ y →
        ((gameGraph (patternGraph A) (lS ++ [v])).Adj x y
          ↔ (gameGraph (patternGraph A) lS).Adj x y)) := by
  have hleg : ∀ z : Fin n, z ∉ insert v S → z ≠ x₀ → z ≠ y₀ →
      schurEntry A S z v = 0 := by
    intro z hz hzx hzy
    have hzS : z ∉ S := fun h => hz (Finset.mem_insert_of_mem h)
    have hzv : z ≠ v :=
      fun hh => hz (hh ▸ Finset.mem_insert_self v S)
    refine schurEntry_eq_zero_of_not_gameAdj hA lS S henum hzv ?_
    intro hAdj
    rcases hN z hzS hzv hAdj.symm with hh | hh
    · exact hzx hh
    · exact hzy hh
  refine ⟨?_, ?_, ?_⟩
  · intro x hxS hxv hAdj
    rcases hN x hxS hxv hAdj with rfl | rfl
    · exact hex
    · exact hey
  · intro x y hx hy hxy hpair
    apply schurEntry_insert_eq_of_leg_zero hA S hv hx hy
    by_cases hxx : x = x₀
    · by_cases hyy : y = y₀
      · exact absurd (Or.inl ⟨hxx, hyy⟩) hpair
      · exact Or.inr (hleg y hy (fun hh => hxy (hxx.trans hh.symm))
          hyy)
    · by_cases hxy₀ : x = y₀
      · by_cases hyx : y = x₀
        · exact absurd (Or.inr ⟨hxy₀, hyx⟩) hpair
        · exact Or.inr (hleg y hy hyx
            (fun hh => hxy (hxy₀.trans hh.symm)))
      · exact Or.inl (hleg x hx hxx hxy₀)
  · intro x y hx hy hxy
    have hxS : x ∉ S := fun h => hx (Finset.mem_insert_of_mem h)
    have hyS : y ∉ S := fun h => hy (Finset.mem_insert_of_mem h)
    have hxv : x ≠ v :=
      fun hh => hx (hh ▸ Finset.mem_insert_self v S)
    have hyv : y ≠ v :=
      fun hh => hy (hh ▸ Finset.mem_insert_self v S)
    rw [gameGraph_append_singleton, elimStep_adj_iff_of_ne hxy]
    constructor
    · rintro (h | ⟨hxA, hyA⟩)
      · exact h
      · have h1 : x = x₀ ∨ x = y₀ := hN x hxS hxv hxA.symm
        have h2 : y = x₀ ∨ y = y₀ := hN y hyS hyv hyA.symm
        rcases h1 with hx1 | hx1 <;> rcases h2 with hy1 | hy1
        · exact absurd (hx1.trans hy1.symm) hxy
        · rw [hx1, hy1]
          exact hadj
        · rw [hx1, hy1]
          exact hadj.symm
        · exact absurd (hx1.trans hy1.symm) hxy
    · intro h
      exact Or.inl h




/-- Closing a path of length at least two with a back edge that is
not already used gives a cycle. -/
theorem isCycle_append_edge {G : SimpleGraph (Fin n)} {x y : Fin n} (p : G.Walk x y)
    (hp : p.IsPath) (hxy : x ≠ y) (hadj : G.Adj y x)
    (hlen : 2 ≤ p.length) (he : s(y, x) ∉ p.edges) :
    (p.append (SimpleGraph.Walk.cons hadj
      SimpleGraph.Walk.nil)).IsCycle := by
  classical
  obtain ⟨w, h', q, hp'⟩ := exists_cons_of_ne hxy p
  have hsupp : p.support = x :: q.support := by
    rw [hp', SimpleGraph.Walk.support_cons]
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [SimpleGraph.Walk.edges_append]
    have hqe : (SimpleGraph.Walk.cons hadj
        SimpleGraph.Walk.nil).edges = [s(y, x)] := by
      rw [SimpleGraph.Walk.edges_cons]
      simp
    rw [hqe, List.nodup_append]
    refine ⟨hp.edges_nodup, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    exact he ((hab.trans hb) ▸ ha)
  · intro hnil
    have hl := congrArg SimpleGraph.Walk.length hnil
    simp only [SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
      at hl
    omega
  · have hsupp2 : (p.append (SimpleGraph.Walk.cons hadj
        SimpleGraph.Walk.nil)).support = x :: (q.support ++ [x]) := by
      rw [SimpleGraph.Walk.support_append, hsupp]
      simp [SimpleGraph.Walk.support_cons]
    rw [hsupp2]
    rw [List.tail_cons]
    have hnd : (x :: q.support).Nodup := by
      rw [← hsupp]
      exact hp.support_nodup
    obtain ⟨hxq, hqnd⟩ := List.nodup_cons.mp hnd
    rw [List.nodup_append]
    refine ⟨hqnd, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    exact hxq ((hab.trans hb) ▸ ha)



/-- The first arc of a cycle (up to a vertex other than the start)
is a path. -/
theorem isPath_takeUntil_of_isCycle {G : SimpleGraph (Fin n)} {v : Fin n} (c : G.Walk v v)
    (hc : c.IsCycle) {y : Fin n} (hy : y ∈ c.support)
    (hvy : y ≠ v) : (c.takeUntil y hy).IsPath := by
  classical
  have hidx : c.support.idxOf y < c.length := by
    have h1 : c.support.idxOf y ≤ c.length := by
      have h2 := List.idxOf_lt_length_of_mem hy
      rw [SimpleGraph.Walk.length_support] at h2
      omega
    refine lt_of_le_of_ne h1 (fun heq => ?_)
    have h2 : c.getVert (c.support.idxOf y) = y :=
      c.getVert_support_idxOf hy
    rw [heq, SimpleGraph.Walk.getVert_length] at h2
    exact hvy h2.symm
  rw [SimpleGraph.Walk.takeUntil_eq_take]
  exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr
    (hc.isPath_take hidx)



/-- The second arc of a cycle (from a vertex other than the start)
is a path. -/
theorem isPath_dropUntil_of_isCycle {G : SimpleGraph (Fin n)} {v : Fin n} (c : G.Walk v v)
    (hc : c.IsCycle) {y : Fin n} (hy : y ∈ c.support)
    (hvy : y ≠ v) : (c.dropUntil y hy).IsPath := by
  classical
  apply SimpleGraph.Walk.IsPath.mk'
  have htailnd : c.support.tail.Nodup := hc.support_nodup
  have hsuff := c.support_dropUntil_suffix_support hy
  obtain ⟨l₀, hl₀⟩ := hsuff
  have hsup : c.support = v :: c.support.tail := by
    have hne : c.support ≠ [] := by
      intro hh
      exact absurd (hh ▸ c.start_mem_support) (by simp)
    obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil hne
    have ha : a = v := by
      have h0 : c.getVert 0 = v := c.getVert_zero
      have h1 : c.getVert 0
          = c.support[0]'(by
            rw [SimpleGraph.Walk.length_support]
            omega) :=
        c.getVert_eq_support_getElem (by omega)
      simp [ht] at h1
      exact h1.symm
    rw [ht, ha]
    simp
  cases l₀ with
  | nil =>
    simp only [List.nil_append] at hl₀
    have hlen : (c.dropUntil y hy).length = c.length := by
      have h1 : (c.dropUntil y hy).support.length
          = c.support.length := by rw [← hl₀]
      simp only [SimpleGraph.Walk.length_support] at h1
      omega
    rw [SimpleGraph.Walk.length_dropUntil] at hlen
    have hL : 3 ≤ c.length := hc.isCircuit.three_le_length
    have hidx0 : c.support.idxOf y = 0 := by omega
    have h2 : c.getVert (c.support.idxOf y) = y :=
      c.getVert_support_idxOf hy
    rw [hidx0, SimpleGraph.Walk.getVert_zero] at h2
    exact absurd h2.symm hvy
  | cons a l₀ =>
    have htail : c.support.tail
        = l₀ ++ (c.dropUntil y hy).support := by
      have h2 : v :: c.support.tail
          = a :: (l₀ ++ (c.dropUntil y hy).support) := by
        rw [← hsup]
        exact hl₀.symm
      exact (List.cons.inj h2).2
    have hsub : (c.dropUntil y hy).support.Sublist c.support.tail :=
      htail ▸ List.sublist_append_right _ _
    exact hsub.nodup htailnd



/-- A walk of length one has a single, explicit edge. -/
theorem edges_of_length_one {G : SimpleGraph (Fin n)} {x y : Fin n} (p : G.Walk x y)
    (h : p.length = 1) : p.edges = [s(x, y)] := by
  cases p with
  | nil => simp at h
  | cons hw q =>
    cases q with
    | nil => simp [SimpleGraph.Walk.edges_cons]
    | cons _ _ => simp [SimpleGraph.Walk.length_cons] at h



/-- Splitting a cycle along a chord gives two strictly shorter
cycles whose supports cover, and are contained in, the original. -/
theorem cycle_split {G : SimpleGraph (Fin n)} {v : Fin n} (c : G.Walk v v) (hc : c.IsCycle)
    {x y : Fin n} (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxy : x ≠ y) (hadj : G.Adj x y) (he : s(x, y) ∉ c.edges) :
    ∃ (a : Fin n) (c₁ : G.Walk a a) (b : Fin n) (c₂ : G.Walk b b),
      c₁.IsCycle ∧ c₂.IsCycle ∧ c₁.length < c.length
        ∧ c₂.length < c.length
        ∧ (∀ z ∈ c₁.support, z ∈ c.support)
        ∧ (∀ z ∈ c₂.support, z ∈ c.support)
        ∧ (∀ z ∈ c.support, z ∈ c₁.support ∨ z ∈ c₂.support) := by
  classical
  set c' := c.rotate x hx with hc'def
  have hc' : c'.IsCycle := hc.rotate hx
  have hlen' : c'.length = c.length := c.length_rotate x hx
  have hy' : y ∈ c'.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).mpr hy
  have he' : s(x, y) ∉ c'.edges := by
    intro h
    exact he ((SimpleGraph.Walk.rotate_edges c x hx).perm.mem_iff
      |>.mp h)
  set p₁ := c'.takeUntil y hy' with hp₁def
  set p₂ := c'.dropUntil y hy' with hp₂def
  have hp₁ : p₁.IsPath := isPath_takeUntil_of_isCycle c' hc' hy'
    ((Ne.symm hxy))
  have hp₂ : p₂.IsPath := isPath_dropUntil_of_isCycle c' hc' hy'
    ((Ne.symm hxy))
  have hsum : p₁.length + p₂.length = c.length := by
    rw [hp₁def, hp₂def, SimpleGraph.Walk.length_takeUntil,
      SimpleGraph.Walk.length_dropUntil, ← hlen']
    have hidx : c'.support.idxOf y ≤ c'.length := by
      have h2 := List.idxOf_lt_length_of_mem hy'
      rw [SimpleGraph.Walk.length_support] at h2
      omega
    omega
  have hge : ∀ (p : G.Walk x y), p.edges ⊆ c'.edges →
      2 ≤ p.length := by
    intro p hsub
    by_contra hlt
    push Not at hlt
    have hne : p.length ≠ 0 := by
      intro h0
      have hA : p.getVert 0 = x := p.getVert_zero
      have hB : p.getVert 0 = y := by
        have h2 : p.getVert p.length = y := p.getVert_length
        rwa [h0] at h2
      exact hxy (hA.symm.trans hB)
    have h1 : p.length = 1 := by omega
    have h2 : s(x, y) ∈ p.edges := by
      rw [edges_of_length_one p h1]
      simp
    exact he' (hsub h2)
  have hl1 : 2 ≤ p₁.length :=
    hge p₁ (SimpleGraph.Walk.edges_takeUntil_subset_edges c' hy')
  have hl2 : 2 ≤ p₂.length := by
    -- p₂ goes from y to x; use the reverse orientation bound via
    -- its edge set after swapping the endpoint names
    by_contra hlt
    push Not at hlt
    have hne : p₂.length ≠ 0 := by
      intro h0
      have h1 : p₂.getVert 0 = y := p₂.getVert_zero
      have h2 : p₂.getVert 0 = x := by
        have h3 : p₂.getVert p₂.length = x := p₂.getVert_length
        rwa [h0] at h3
      exact hxy (h2.symm.trans h1)
    have h1 : p₂.length = 1 := by omega
    have h2 : s(y, x) ∈ p₂.edges := by
      rw [edges_of_length_one p₂ h1]
      simp
    have h3 : s(x, y) ∈ c'.edges := by
      have h4 := SimpleGraph.Walk.edges_dropUntil_subset_edges c'
        hy' h2
      rwa [Sym2.eq_swap] at h4
    exact he' h3
  have he1 : s(y, x) ∉ p₁.edges := by
    intro h
    have h2 := SimpleGraph.Walk.edges_takeUntil_subset_edges c'
      hy' h
    rw [Sym2.eq_swap] at h2
    exact he' h2
  have he2 : s(x, y) ∉ p₂.edges := by
    intro h
    exact he' (SimpleGraph.Walk.edges_dropUntil_subset_edges c'
      hy' h)
  refine ⟨x, p₁.append (SimpleGraph.Walk.cons hadj.symm
      SimpleGraph.Walk.nil),
    y, p₂.append (SimpleGraph.Walk.cons hadj
      SimpleGraph.Walk.nil),
    isCycle_append_edge p₁ hp₁ hxy hadj.symm hl1 he1,
    isCycle_append_edge p₂ hp₂ (Ne.symm hxy) hadj hl2 he2,
    by simp only [SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_nil]; omega,
    by simp only [SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_nil]; omega,
    ?_, ?_, ?_⟩
  · intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    have hzc : z ∈ c'.support := by
      rcases hz with hz | hz
      · exact c'.support_takeUntil_subset_support hy' hz
      · have hqs : (SimpleGraph.Walk.cons hadj.symm
            SimpleGraph.Walk.nil).support = [y, x] := by
          simp [SimpleGraph.Walk.support_cons]
        rw [hqs] at hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact hy'
        · exact c'.start_mem_support
    exact (SimpleGraph.Walk.mem_support_rotate_iff c x hx).mp hzc
  · intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    have hzc : z ∈ c'.support := by
      rcases hz with hz | hz
      · exact c'.support_dropUntil_subset_support hy' hz
      · have hqs : (SimpleGraph.Walk.cons hadj
            SimpleGraph.Walk.nil).support = [x, y] := by
          simp [SimpleGraph.Walk.support_cons]
        rw [hqs] at hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact c'.start_mem_support
        · exact hy'
    exact (SimpleGraph.Walk.mem_support_rotate_iff c x hx).mp hzc
  · intro z hz
    have hzc : z ∈ c'.support :=
      (SimpleGraph.Walk.mem_support_rotate_iff c x hx).mpr hz
    rw [← SimpleGraph.Walk.take_spec c' hy',
      SimpleGraph.Walk.mem_support_append_iff] at hzc
    rcases hzc with hz1 | hz2
    · exact Or.inl (by
        rw [SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inl hz1)
    · exact Or.inr (by
        rw [SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inl hz2)



/-- The edges of a walk induced on a vertex set are the original
edges, read through the subtype coercion. -/
theorem edges_induce_map_val {G : SimpleGraph (Fin n)} {s : Set (Fin n)} {v : Fin n}
    (c : G.Walk v v) (hw : ∀ x ∈ c.support, x ∈ s) :
    (c.induce s hw).edges.map (Sym2.map Subtype.val) = c.edges := by
  have h1 := congrArg SimpleGraph.Walk.edges
    (SimpleGraph.Walk.map_induce c hw)
  rwa [SimpleGraph.Walk.edges_map] at h1



/-- Induced cycles: a cycle transports to an induced subgraph
containing its support, with length preserved. -/
theorem isCycle_induce {G : SimpleGraph (Fin n)} {s : Set (Fin n)} {v : Fin n}
    (c : G.Walk v v) (hc : c.IsCycle)
    (hw : ∀ x ∈ c.support, x ∈ s) :
    (c.induce s hw).IsCycle ∧ (c.induce s hw).length = c.length := by
  classical
  have hlen : (c.induce s hw).length = c.length := by
    have h1 := congrArg SimpleGraph.Walk.length
      (SimpleGraph.Walk.map_induce c hw)
    rwa [SimpleGraph.Walk.length_map] at h1
  refine ⟨?_, hlen⟩
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · exact List.Nodup.of_map _
      ((edges_induce_map_val c hw) ▸ hc.edges_nodup)
  · intro hnil
    have h1 := congrArg SimpleGraph.Walk.length hnil
    simp only [SimpleGraph.Walk.length_nil] at h1
    have h3 := hc.isCircuit.three_le_length
    omega
  · have key : (c.induce s hw).support.tail.map Subtype.val
        = c.support.tail := by
      rw [List.map_tail, SimpleGraph.Walk.support_induce]
      simp
    exact List.Nodup.of_map _ (key ▸ hc.support_nodup)



/-- Edge membership transports between a walk and its induced
walk. -/
theorem mem_edges_induce {G : SimpleGraph (Fin n)} {s : Set (Fin n)} {v : Fin n}
    (c : G.Walk v v) (hw : ∀ x ∈ c.support, x ∈ s)
    {a b : ↥s} :
    s(a, b) ∈ (c.induce s hw).edges ↔ s(a.val, b.val) ∈ c.edges := by
  constructor
  · intro h
    have h2 : (Sym2.map Subtype.val) s(a, b)
        ∈ (c.induce s hw).edges.map (Sym2.map Subtype.val) :=
      List.mem_map_of_mem h
    rwa [edges_induce_map_val c hw] at h2
  · intro h
    rw [← edges_induce_map_val c hw] at h
    rw [List.mem_map] at h
    obtain ⟨e, he, hfe⟩ := h
    obtain ⟨x, y, hab⟩ : ∃ x y, s(x, y) = e :=
      (Sym2.exists (f := fun z => z = e)).mp ⟨e, rfl⟩
    subst hab
    rw [Sym2.map_mk, Sym2.eq_iff] at hfe
    rcases hfe with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [Subtype.ext hx, Subtype.ext hy] at he
      exact he
    · rw [Subtype.ext hx, Subtype.ext hy, Sym2.eq_swap] at he
      exact he



/-- **Master cycle exclusion.** In a chordal graph, every cycle is
supported on the unique triangle: a shortest cycle meeting the
complement of `T` would be chordless (a chord splits it into two
shorter cycles, one still meeting the complement), hence a chordal
3-cycle, hence a second triangle. -/
theorem cycle_support_subset_T {G : SimpleGraph (Fin n)} (hG : IsChordal G)
    {T : Finset (Fin n)}
    (huniq : ∀ T' : Finset (Fin n), T'.card = 3 →
      G.IsClique (↑T' : Set (Fin n)) → T' = T)
    {v : Fin n} (c : G.Walk v v) (hc : c.IsCycle) :
    ∀ z ∈ c.support, z ∈ T := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hz, hzT⟩ := hcon
  set P : ℕ → Prop := fun L => ∃ (w : Fin n) (c₀ : G.Walk w w),
    c₀.IsCycle ∧ (∃ z ∈ c₀.support, z ∉ T) ∧ c₀.length = L with hPdef
  have hPex : ∃ L, P L := ⟨c.length, v, c, hc, ⟨z, hz, hzT⟩, rfl⟩
  obtain ⟨v₀, c₀, hc₀, ⟨z₀, hz₀, hz₀T⟩, hlen₀⟩ := Nat.find_spec hPex
  have hmin : ∀ (w : Fin n) (c' : G.Walk w w), c'.IsCycle →
      (∃ z ∈ c'.support, z ∉ T) → c₀.length ≤ c'.length := by
    intro w c' hc' hz'
    have hle := Nat.find_min' hPex
      (show P c'.length from ⟨w, c', hc', hz', rfl⟩)
    omega
  have hchord : ∀ x ∈ c₀.support, ∀ y ∈ c₀.support, G.Adj x y →
      s(x, y) ∈ c₀.edges := by
    intro x hx y hy hadj
    by_contra he
    obtain ⟨a, c₁, b, c₂, hc1, hc2, hl1, hl2, -, -, hcover⟩ :=
      cycle_split c₀ hc₀ hx hy hadj.ne hadj he
    rcases hcover z₀ hz₀ with hz1 | hz2
    · exact absurd (hmin a c₁ hc1 ⟨z₀, hz1, hz₀T⟩)
        (not_le_of_gt hl1)
    · exact absurd (hmin b c₂ hc2 ⟨z₀, hz2, hz₀T⟩)
        (not_le_of_gt hl2)
  set s : Finset (Fin n) := c₀.support.toFinset with hsdef
  have hw : ∀ x ∈ c₀.support, x ∈ (↑s : Set (Fin n)) := by
    intro x hx
    rw [hsdef]
    exact List.mem_toFinset.mpr hx
  obtain ⟨hc0i, hleni⟩ := isCycle_induce c₀ hc₀ hw
  have hL : (c₀.induce (↑s) hw).length < 4 := by
    refine hG s _ _ hc0i ?_ ?_
    · intro e he
      obtain ⟨a, b, hab⟩ : ∃ a b, s(a, b) = e :=
        (Sym2.exists (f := fun z => z = e)).mp ⟨e, rfl⟩
      subst hab
      have hadj : (G.induce (↑s : Set (Fin n))).Adj a b :=
        (SimpleGraph.mem_edgeSet _).mp he
      rw [SimpleGraph.induce_adj] at hadj
      have ha : a.val ∈ c₀.support :=
        List.mem_toFinset.mp (hsdef ▸ Finset.mem_coe.mp a.2)
      have hb : b.val ∈ c₀.support :=
        List.mem_toFinset.mp (hsdef ▸ Finset.mem_coe.mp b.2)
      exact (mem_edges_induce c₀ hw).mpr (hchord a.val ha b.val hb hadj)
    · intro z hz
      have hzsup : z ∈ c₀.support :=
        List.mem_toFinset.mp (hsdef ▸ Finset.mem_coe.mp hz)
      have hmap : (c₀.induce (↑s) hw).support.map Subtype.val
          = c₀.support := by
        rw [SimpleGraph.Walk.support_induce]
        simp
      have h2 : z ∈ (c₀.induce (↑s) hw).support.map Subtype.val :=
        hmap ▸ hzsup
      rw [List.mem_map] at h2
      obtain ⟨a, ha, haz⟩ := h2
      exact ⟨a, ha, haz⟩
  have hL3 : c₀.length = 3 := by
    have h3 := hc₀.isCircuit.three_le_length
    omega
  -- extract the triangle
  set a := c₀.getVert 0 with hadef
  set b := c₀.getVert 1 with hbdef
  set d := c₀.getVert 2 with hddef
  have ha0 : a = v₀ := c₀.getVert_zero
  have hadj1 : G.Adj a b := c₀.adj_getVert_succ (by omega)
  have hadj2 : G.Adj b d := c₀.adj_getVert_succ (by omega)
  have hadj3 : G.Adj d a := by
    have h3 : G.Adj (c₀.getVert 2) (c₀.getVert (2 + 1)) :=
      c₀.adj_getVert_succ (by omega)
    have h4 : c₀.getVert (2 + 1) = a := by
      rw [show (2 + 1 : ℕ) = c₀.length by omega,
        SimpleGraph.Walk.getVert_length]
      exact ha0.symm
    exact h4 ▸ h3
  have hinj := hc₀.getVert_injOn'
  have hab : a ≠ b := by
    intro h
    have h2 := hinj (show (0 : ℕ) ∈ {i | i ≤ c₀.length - 1} by
      simp [hL3]) (show (1 : ℕ) ∈ {i | i ≤ c₀.length - 1} by
      simp [hL3]) h
    omega
  have had : a ≠ d := by
    intro h
    have h2 := hinj (show (0 : ℕ) ∈ {i | i ≤ c₀.length - 1} by
      simp [hL3]) (show (2 : ℕ) ∈ {i | i ≤ c₀.length - 1} by
      simp [hL3]) h
    omega
  have hbd : b ≠ d := by
    intro h
    have h2 := hinj (show (1 : ℕ) ∈ {i | i ≤ c₀.length - 1} by
      simp [hL3]) (show (2 : ℕ) ∈ {i | i ≤ c₀.length - 1} by
      simp [hL3]) h
    omega
  have hz0mem : z₀ = a ∨ z₀ = b ∨ z₀ = d := by
    have hz0eq : z₀ = c₀.getVert (c₀.support.idxOf z₀) :=
      (c₀.getVert_support_idxOf hz₀).symm
    have hidxlt : c₀.support.idxOf z₀ < 4 := by
      have h2 := List.idxOf_lt_length_of_mem hz₀
      rw [SimpleGraph.Walk.length_support] at h2
      omega
    have hcases : c₀.support.idxOf z₀ = 0 ∨ c₀.support.idxOf z₀ = 1
        ∨ c₀.support.idxOf z₀ = 2 ∨ c₀.support.idxOf z₀ = 3 := by
      omega
    rcases hcases with h | h | h | h
    · exact Or.inl (by rw [hz0eq, h])
    · exact Or.inr (Or.inl (by rw [hz0eq, h]))
    · exact Or.inr (Or.inr (by rw [hz0eq, h]))
    · refine Or.inl ?_
      rw [hz0eq, h]
      have h3 : c₀.getVert 3 = v₀ := by
        rw [show (3 : ℕ) = c₀.length from hL3.symm]
        exact c₀.getVert_length
      rw [h3]
      exact ha0.symm
  have hcard : ({a, b, d} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, had]),
      Finset.card_insert_of_notMem (by simp [hbd]),
      Finset.card_singleton]
  have hclique : G.IsClique (↑({a, b, d} : Finset (Fin n)) :
      Set (Fin n)) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact hadj1
    · exact hadj3.symm
    · exact hadj1.symm
    · exact absurd rfl hxy
    · exact hadj2
    · exact hadj3
    · exact hadj2.symm
    · exact absurd rfl hxy
  have hne : ({a, b, d} : Finset (Fin n)) ≠ T := by
    intro hTT
    apply hz₀T
    rw [← hTT]
    rcases hz0mem with rfl | rfl | rfl <;> simp
  exact hne (huniq _ hcard hclique)




/-- A path of maximal length among paths from `a` with support in
`U` exists. -/
theorem exists_maximal_path_in {G : SimpleGraph (Fin n)}
    {U : Finset (Fin n)} {a : Fin n}
    (ha : a ∈ U) :
    ∃ (b : Fin n) (q : G.Walk a b), q.IsPath ∧
      (∀ z ∈ q.support, z ∈ U) ∧
      ∀ (b' : Fin n) (q' : G.Walk a b'), q'.IsPath →
        (∀ z ∈ q'.support, z ∈ U) → q'.length ≤ q.length := by
  classical
  set s : Set ℕ := {L | ∃ (b : Fin n) (q : G.Walk a b), q.IsPath ∧
    (∀ z ∈ q.support, z ∈ U) ∧ q.length = L} with hsdef
  have hfin : s.Finite := by
    refine Set.Finite.subset (Set.finite_le_nat n) ?_
    rintro L ⟨b, q, hq, -, rfl⟩
    have hlt : q.length < Fintype.card (Fin n) := hq.length_lt
    rw [Fintype.card_fin] at hlt
    simp only [Set.mem_ofPred_eq]
    omega
  have hne : s.Nonempty :=
    ⟨0, a, SimpleGraph.Walk.nil, by simp,
      fun z hz => by
        simp only [SimpleGraph.Walk.support_nil,
          List.mem_singleton] at hz
        exact hz ▸ ha, rfl⟩
  obtain ⟨L, ⟨⟨b, q, hq, hqU, hlen⟩, hmax⟩⟩ :=
    hfin.exists_maximal hne
  refine ⟨b, q, hq, hqU, fun b' q' hq' hqU' => ?_⟩
  have h2 := hmax ⟨b', q', hq', hqU', rfl⟩
  omega



/-- The endpoint of a maximal path has all its `U`-neighbours on
the path. -/
theorem maximal_endpoint_mem {G : SimpleGraph (Fin n)}
    {U : Finset (Fin n)} {a b : Fin n}
    (q : G.Walk a b) (hq : q.IsPath)
    (hqU : ∀ z ∈ q.support, z ∈ U)
    (hqmax : ∀ (b' : Fin n) (q' : G.Walk a b'), q'.IsPath →
      (∀ z ∈ q'.support, z ∈ U) → q'.length ≤ q.length) :
    ∀ x ∈ U, G.Adj b x → x ∈ q.support := by
  classical
  intro x hxU hadj
  by_contra hxsupp
  have hpath : (q.append (SimpleGraph.Walk.cons hadj
      SimpleGraph.Walk.nil)).IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    rw [SimpleGraph.Walk.support_append]
    have hqs : (SimpleGraph.Walk.cons hadj
        SimpleGraph.Walk.nil).support = [b, x] := by
      simp [SimpleGraph.Walk.support_cons]
    rw [hqs]
    change (q.support ++ [x]).Nodup
    rw [List.nodup_append]
    refine ⟨hq.support_nodup, by simp, ?_⟩
    intro z hz w hw hzw
    simp only [List.mem_singleton] at hw
    exact hxsupp ((hzw.trans hw) ▸ hz)
  have hlen := hqmax x _ hpath (by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact hqU z hz
    · have hqs : (SimpleGraph.Walk.cons hadj
          SimpleGraph.Walk.nil).support = [b, x] := by
        simp [SimpleGraph.Walk.support_cons]
      rw [hqs] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hqU z q.end_mem_support
      · exact hxU)
  simp only [SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
    at hlen
  omega



/-- The endpoint of a maximal path inside a cycle-free region `U`
has at most one neighbour in `U`: the predecessor on the path. -/
theorem endpoint_neighbors_eq_pred {G : SimpleGraph (Fin n)}
    {U : Finset (Fin n)} {a b : Fin n} (q : G.Walk a b) (hq : q.IsPath)
    (hqU : ∀ z ∈ q.support, z ∈ U)
    (hmax : ∀ x ∈ U, G.Adj b x → x ∈ q.support)
    (hnocycle : ∀ (w : Fin n) (c : G.Walk w w), c.IsCycle →
      ∀ z ∈ c.support, z ∉ U) :
    ∀ x ∈ U, G.Adj b x → x = q.getVert (q.length - 1) := by
  classical
  intro x hxU hadj
  have hxsupp : x ∈ q.support := hmax x hxU hadj
  have hxb : x ≠ b := Ne.symm hadj.ne
  have hidxle : q.support.idxOf x ≤ q.length := by
    have h2 := List.idxOf_lt_length_of_mem hxsupp
    rw [SimpleGraph.Walk.length_support] at h2
    omega
  set p := q.dropUntil x hxsupp with hpdef
  have hp : p.IsPath := hq.dropUntil hxsupp
  have hplen : p.length = q.length - q.support.idxOf x :=
    SimpleGraph.Walk.length_dropUntil q hxsupp
  by_cases h1 : p.length = 1
  · have hidx : q.support.idxOf x = q.length - 1 := by omega
    have h2 : q.getVert (q.support.idxOf x) = x :=
      q.getVert_support_idxOf hxsupp
    rw [hidx] at h2
    exact h2.symm
  · have hne0 : p.length ≠ 0 := by
      intro h0
      have hidx : q.support.idxOf x = q.length := by omega
      have h2 : q.getVert (q.support.idxOf x) = x :=
        q.getVert_support_idxOf hxsupp
      rw [hidx, SimpleGraph.Walk.getVert_length] at h2
      exact hxb h2.symm
    have hge2 : 2 ≤ p.length := by omega
    have he : s(b, x) ∉ p.edges := by
      intro h
      exact h1 (hp.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ h))
    have hcyc : (p.append (SimpleGraph.Walk.cons hadj
        SimpleGraph.Walk.nil)).IsCycle :=
      isCycle_append_edge p hp hxb hadj hge2 he
    have hbmem : b ∈ (p.append (SimpleGraph.Walk.cons hadj
        SimpleGraph.Walk.nil)).support := by
      rw [SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl p.end_mem_support
    have hbU : b ∈ U := hqU b q.end_mem_support
    exact absurd hbU (hnocycle _ _ hcyc b hbmem)



/-- Closing a path with two extra edges through a fresh vertex
gives a cycle. -/
theorem isCycle_append_two_edges {G : SimpleGraph (Fin n)}
    {t b : Fin n} (P : G.Walk t b)
    (hP : P.IsPath) {t' : Fin n} (h1 : G.Adj b t') (h2 : G.Adj t' t)
    (ht' : t' ∉ P.support) (hbt : b ≠ t) (htt' : t ≠ t')
    (hlen : 1 ≤ P.length) :
    ((P.append (SimpleGraph.Walk.cons h1 SimpleGraph.Walk.nil)).append
      (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)).IsCycle := by
  classical
  have htP : t ∈ P.support := P.start_mem_support
  have hbP : b ∈ P.support := P.end_mem_support
  have ht'edges : ∀ e ∈ P.edges, e ≠ s(b, t') := by
    intro e he hcon
    have h2 : t' ∈ P.support := by
      have h3 := P.snd_mem_support_of_mem_edges (hcon ▸ he)
      exact h3
    exact ht' h2
  have htfresh : s(t', t) ∉ P.edges := by
    intro h
    exact ht' (P.fst_mem_support_of_mem_edges h)
  obtain ⟨w, h', q, hP'⟩ := exists_cons_of_ne (Ne.symm hbt) P
  have hsupp : P.support = t :: q.support := by
    rw [hP', SimpleGraph.Walk.support_cons]
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_append]
    have e1 : (SimpleGraph.Walk.cons h1
        SimpleGraph.Walk.nil).edges = [s(b, t')] := by
      rw [SimpleGraph.Walk.edges_cons]
      simp
    have e2 : (SimpleGraph.Walk.cons h2
        SimpleGraph.Walk.nil).edges = [s(t', t)] := by
      rw [SimpleGraph.Walk.edges_cons]
      simp
    rw [e1, e2, List.nodup_append]
    refine ⟨?_, by simp, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hP.edges_nodup, by simp, ?_⟩
      intro z hz w hw hzw
      simp only [List.mem_singleton] at hw
      exact ht'edges z hz (hzw.trans hw)
    · intro z hz w hw hzw
      simp only [List.mem_append, List.mem_singleton] at hz
      simp only [List.mem_singleton] at hw
      have hzte : z = s(t', t) := hzw.trans hw
      rcases hz with hz | hz
      · exact htfresh (hzte ▸ hz)
      · have h3 : s(b, t') = s(t', t) := hz.symm.trans hzte
        rw [Sym2.eq_iff] at h3
        rcases h3 with ⟨hbb, -⟩ | ⟨hbt₂, htt₂⟩
        · exact ht' (hbb ▸ hbP)
        · exact hbt hbt₂
  · intro hnil
    have hl := congrArg SimpleGraph.Walk.length hnil
    simp only [SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
      at hl
    omega
  · have hsupp2 : ((P.append (SimpleGraph.Walk.cons h1
          SimpleGraph.Walk.nil)).append
        (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)).support
        = t :: (q.support ++ [t', t]) := by
      rw [SimpleGraph.Walk.support_append,
        SimpleGraph.Walk.support_append, hsupp]
      simp [SimpleGraph.Walk.support_cons]
    rw [hsupp2, List.tail_cons]
    have hnd : (t :: q.support).Nodup := by
      rw [← hsupp]
      exact hP.support_nodup
    obtain ⟨htq, hqnd⟩ := List.nodup_cons.mp hnd
    rw [List.nodup_append]
    refine ⟨hqnd, ?_, ?_⟩
    · rw [List.nodup_cons]
      exact ⟨fun h => by simp at h; exact htt' h.symm, by simp⟩
    · intro z hz w hw hzw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      have hzs : z ∈ P.support := by
        rw [hsupp]
        exact List.mem_cons_of_mem _ hz
      rcases hw with rfl | rfl
      · exact ht' ((hzw).symm ▸ hzs)
      · exact htq ((hzw).symm ▸ hz)




/-- A longest path inside `U` (over all endpoint choices) exists. -/
theorem exists_longest_path_in {G : SimpleGraph (Fin n)}
    {U : Finset (Fin n)} (hne : U.Nonempty) :
    ∃ (a b : Fin n) (q : G.Walk a b), q.IsPath ∧
      (∀ z ∈ q.support, z ∈ U) ∧
      ∀ (a' b' : Fin n) (q' : G.Walk a' b'), q'.IsPath →
        (∀ z ∈ q'.support, z ∈ U) → q'.length ≤ q.length := by
  classical
  set s : Set ℕ := {L | ∃ (a b : Fin n) (q : G.Walk a b), q.IsPath ∧
    (∀ z ∈ q.support, z ∈ U) ∧ q.length = L} with hsdef
  have hfin : s.Finite := by
    refine Set.Finite.subset (Set.finite_le_nat n) ?_
    rintro L ⟨a, b, q, hq, -, rfl⟩
    have hlt : q.length < Fintype.card (Fin n) := hq.length_lt
    rw [Fintype.card_fin] at hlt
    simp only [Set.mem_ofPred_eq]
    omega
  obtain ⟨a₀, ha₀⟩ := hne
  have hne' : s.Nonempty :=
    ⟨0, a₀, a₀, SimpleGraph.Walk.nil, by simp,
      fun z hz => by
        simp only [SimpleGraph.Walk.support_nil,
          List.mem_singleton] at hz
        exact hz ▸ ha₀, rfl⟩
  obtain ⟨L, ⟨⟨a, b, q, hq, hqU, hlen⟩, hmax⟩⟩ :=
    hfin.exists_maximal hne'
  refine ⟨a, b, q, hq, hqU, fun a' b' q' hq' hqU' => ?_⟩
  have h2 := hmax ⟨a', b', q', hq', hqU', rfl⟩
  omega

end CholeskyCancellations

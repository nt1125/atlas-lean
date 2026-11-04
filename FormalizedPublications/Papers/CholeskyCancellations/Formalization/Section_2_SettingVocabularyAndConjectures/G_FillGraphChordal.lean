/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Section_2_SettingVocabularyAndConjectures.F_ConjecturesAndFeasibility

/-! # Sanity checks on the fill graph (paper Section 2)

Paper Remark 2.11 (`rem:fill-sanity`), claim by claim:

* "`G⁺_σ ⊇ G_A`" is `patternGraph_le_fillGraph` (for every list `σ`);
* "`G⁺_σ` is never empty for `n ≥ 2` with `G_A` connected" is `fillGraph_ne_bot`;
* "`G⁺_σ` is chordal and `σ` is a PEO of it (Definition 2.14)" is
  `fillGraph_isPerfectEliminationOrdering` together with `fillGraph_isChordal`; the latter goes
  through `isChordal_of_isPerfectEliminationOrdering`, the easy direction of the
  Fulkerson–Gross characterization [FG65] quoted in paper Remark 2.15 (a graph with a PEO is
  chordal);
* "`G⁺_σ` is exactly the symbolic pattern of `L + Lᵀ` (Definition 2.23)": symbolically this is
  how `fillGraph` is read off (at the committing prefix of each pair, `fillGraph_adj_iff`); its
  factor side is `factorPattern_le_fillGraph`, `Gᴸ_σ ⊆ G⁺_σ`, with equality exactly for clean
  orderings (`clean_iff_factor_pattern`). Both graphs live on the full vertex set `Fin n`, which
  is what the equality `Gᴸ_σ = G⁺_σ` of Conjecture 2.27 compares.
-/

open scoped Matrix

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): vertices `Fin n`, SPD = `Matrix.PosDef`,
levels `Finset (Fin n)`, pivot-order list orderings, Schur entries through `schurEntry` only.
(Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- An ordering lists every vertex (paper Section 2's orderings `σ = (v₁, …, vₙ)` of `V`, as
used in paper Remark 2.11, `rem:fill-sanity`): a duplicate-free list of length `n` exhausts
`Fin n`. -/
theorem fill_mem_of_isOrdering {σ : List (Fin n)} (hσ : IsOrdering σ) (x : Fin n) : x ∈ σ := by
  have h1 : σ.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hσ.1, hσ.2, Fintype.card_fin]
  exact List.mem_toFinset.mp (by rw [h1]; exact Finset.mem_univ x)



/-- `G⁺_σ ⊇ G_A` (paper Remark 2.11, `rem:fill-sanity`, first claim): an edge of `G_A` is an
edge of every game graph (`gameGraph_adj_mono_append` from the empty list), in particular of
the game graph at the committing prefix, where `fillGraph_adj_iff` reads fill adjacency. No
ordering hypothesis is needed. -/
theorem patternGraph_le_fillGraph (A : Matrix (Fin n) (Fin n) ℝ) (σ : List (Fin n)) :
    patternGraph A ≤ fillGraph A σ := by
  intro j k h
  rw [fillGraph_adj_iff]
  exact gameGraph_adj_mono_append (patternGraph A) [] (prefixList σ j k) j k h



/-- `G⁺_σ` is never empty for `n ≥ 2` with `G_A` connected (paper Remark 2.11,
`rem:fill-sanity`): the vertices `0` and `1` are distinct, a walk of `G_A` joining them starts
with an edge of `G_A`, and that edge lies in `G⁺_σ` by `patternGraph_le_fillGraph`. -/
theorem fillGraph_ne_bot (A : Matrix (Fin n) (Fin n) ℝ) (σ : List (Fin n)) (hn : 2 ≤ n)
    (hconn : (patternGraph A).Connected) : fillGraph A σ ≠ ⊥ := by
  intro hbot
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  obtain ⟨w⟩ := hconn.preconnected ⟨0, by omega⟩ ⟨1, by omega⟩
  obtain ⟨x, hadj, -, -⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne h01 w
  have hfill := patternGraph_le_fillGraph A σ hadj
  rw [hbot] at hfill
  exact (SimpleGraph.bot_adj _ _).mp hfill



/-- Two distinct vertices are comparable in an ordering: one comes after the other (paper
Section 2's orderings; used for the PEO claim of paper Remark 2.11, `rem:fill-sanity`). -/
theorem fill_afterIn_or_afterIn {σ : List (Fin n)} (hσ : IsOrdering σ) {j k : Fin n}
    (hjk : j ≠ k) : AfterIn σ j k ∨ AfterIn σ k j := by
  obtain ⟨l₁, t, hσeq⟩ := List.append_of_mem (fill_mem_of_isOrdering hσ j)
  have hk : k ∈ l₁ ++ j :: t := hσeq ▸ fill_mem_of_isOrdering hσ k
  rcases List.mem_append.mp hk with hk | hk
  · obtain ⟨m₁, m₂, hl₁⟩ := List.append_of_mem hk
    exact Or.inr ⟨m₁, m₂, t, by rw [hσeq, hl₁]⟩
  · rcases List.mem_cons.mp hk with hk | hk
    · exact absurd hk.symm hjk
    · obtain ⟨m₁, m₂, ht⟩ := List.append_of_mem hk
      exact Or.inl ⟨l₁, m₁, m₂, by simp [hσeq, ht]⟩



/-- If `v` precedes `j` in an ordering, every predecessor of `v` precedes `j`: the predecessor
lists `prefixListBefore σ v ⊆ prefixListBefore σ j` (the sets `S` of paper Proposition 2.10
are nested along `σ`; used for the PEO claim of paper Remark 2.11, `rem:fill-sanity`). Both are
prefixes of `σ`, hence comparable, and `v` lies in the second but not in the first. -/
theorem fill_prefixListBefore_subset {σ : List (Fin n)} (hσ : IsOrdering σ) {v j : Fin n}
    (h : AfterIn σ v j) {x : Fin n} (hx : x ∈ prefixListBefore σ v) :
    x ∈ prefixListBefore σ j := by
  have hvj : v ∈ prefixListBefore σ j := mem_prefixListBefore_of_afterIn hσ h
  have hpv : prefixListBefore σ v <+: σ := List.takeWhile_prefix _
  have hpj : prefixListBefore σ j <+: σ := List.takeWhile_prefix _
  rcases List.prefix_or_prefix_of_prefix hpv hpj with hp | hp
  · exact hp.subset hx
  · exact absurd (hp.subset hvj) (not_mem_prefixListBefore_self σ v)



/-- The PEO step for `G⁺_σ` (paper Remark 2.11, `rem:fill-sanity`): if `v` precedes `j`, `j`
precedes `k`, and `v` is fill-adjacent to both, then `j` and `k` are fill-adjacent. By the
fill-path theorem (`fill_path`, paper Proposition 2.10) there are `v`–`j` and `v`–`k` walks in
`G_A` whose interior vertices precede `v`; joined at `v` they give a `j`–`k` walk whose interior
vertices precede `j`, i.e. lie in the committing prefix of `{j, k}`. -/
theorem fill_adj_of_common_earlier {A : Matrix (Fin n) (Fin n) ℝ} {σ : List (Fin n)}
    (hσ : IsOrdering σ) {v j k : Fin n} (hvj : (fillGraph A σ).Adj v j)
    (hvk : (fillGraph A σ).Adj v k) (havj : AfterIn σ v j) (havk : AfterIn σ v k)
    (hajk : AfterIn σ j k) (hjk : j ≠ k) : (fillGraph A σ).Adj j k := by
  obtain ⟨w₁, hw₁⟩ :=
    (fill_path σ hσ v j hvj.ne).2.mp ((fill_path σ hσ v j hvj.ne).1.mp hvj)
  obtain ⟨w₂, hw₂⟩ :=
    (fill_path σ hσ v k hvk.ne).2.mp ((fill_path σ hσ v k hvk.ne).1.mp hvk)
  have hPj : prefixSet σ v j = (prefixListBefore σ v).toFinset := by
    rw [prefixSet, prefixList_eq_prefixListBefore_cons_of_afterIn σ hσ havj]
  have hPk : prefixSet σ v k = (prefixListBefore σ v).toFinset := by
    rw [prefixSet, prefixList_eq_prefixListBefore_cons_of_afterIn σ hσ havk]
  have hT : prefixSet σ j k = (prefixListBefore σ j).toFinset := by
    rw [prefixSet, prefixList_eq_prefixListBefore_cons_of_afterIn σ hσ hajk]
  have hvT : v ∈ prefixSet σ j k := by
    rw [hT, List.mem_toFinset]
    exact mem_prefixListBefore_of_afterIn hσ havj
  have hPT : ∀ x ∈ (prefixListBefore σ v).toFinset, x ∈ prefixSet σ j k := by
    intro x hx
    rw [hT, List.mem_toFinset]
    exact fill_prefixListBefore_subset hσ havj (List.mem_toFinset.mp hx)
  refine (fill_path σ hσ j k hjk).1.mpr
    ((fill_path σ hσ j k hjk).2.mpr ⟨w₁.reverse.append w₂, ?_⟩)
  intro x hx
  rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
    List.mem_reverse] at hx
  rcases hx with hx | hx
  · rcases hw₁ x hx with hxv | hxj | hxS
    · exact Or.inr (Or.inr (hxv ▸ hvT))
    · exact Or.inl hxj
    · rw [hPj] at hxS
      exact Or.inr (Or.inr (hPT x hxS))
  · rcases hw₂ x hx with hxv | hxk | hxS
    · exact Or.inr (Or.inr (hxv ▸ hvT))
    · exact Or.inr (Or.inl hxk)
    · rw [hPk] at hxS
      exact Or.inr (Or.inr (hPT x hxS))



/-- `σ` is a perfect elimination ordering of `G⁺_σ` (paper Remark 2.11, `rem:fill-sanity`, with
PEO as in paper Definition 2.14 and Remark 2.15): the later fill neighbours of every vertex are
pairwise fill-adjacent (`fill_adj_of_common_earlier`, after ordering the two neighbours along
`σ` with `fill_afterIn_or_afterIn`). -/
theorem fillGraph_isPerfectEliminationOrdering (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : List (Fin n)) (hσ : IsOrdering σ) :
    IsPerfectEliminationOrdering (fillGraph A σ) σ := by
  refine ⟨hσ, fun v => ?_⟩
  intro j hj k hk hjk
  obtain ⟨hvj, havj⟩ := hj
  obtain ⟨hvk, havk⟩ := hk
  rcases fill_afterIn_or_afterIn hσ hjk with hajk | hakj
  · exact fill_adj_of_common_earlier hσ hvj hvk havj havk hajk hjk
  · exact (fill_adj_of_common_earlier hσ hvk hvj havk havj hakj (Ne.symm hjk)).symm



/-- The `σ`-earliest member of a set: a list meeting `s` splits as `l₁ ++ m :: t` with `m ∈ s`
and no member of `s` in `l₁` (the earliest vertex used in the easy direction of [FG65], paper
Remark 2.15, for the chordality claim of paper Remark 2.11, `rem:fill-sanity`). -/
theorem peo_exists_first_mem (s : Finset (Fin n)) :
    ∀ σ : List (Fin n), (∃ x ∈ σ, x ∈ s) →
      ∃ (l₁ : List (Fin n)) (m : Fin n) (t : List (Fin n)),
        σ = l₁ ++ m :: t ∧ m ∈ s ∧ ∀ y ∈ l₁, y ∉ s
  | [], ⟨x, hx, _⟩ => by simp at hx
  | a :: σ, ⟨x, hx, hxs⟩ => by
    by_cases ha : a ∈ s
    · exact ⟨[], a, σ, rfl, ha, by simp⟩
    · have hx' : x ∈ σ := by
        rcases List.mem_cons.mp hx with hxa | hx'
        · exact absurd (hxa ▸ hxs) ha
        · exact hx'
      obtain ⟨l₁, m, t, hσ, hm, hl₁⟩ := peo_exists_first_mem s σ ⟨x, hx', hxs⟩
      refine ⟨a :: l₁, m, t, by simp [hσ], hm, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with hya | hy
      · exact hya ▸ ha
      · exact hl₁ y hy



/-- In a cycle of length at least four, the two cycle-neighbours of the base vertex are not
joined by an edge of the cycle, so in an induced cycle of length at least 4 (paper
Definition 2.14) they are not adjacent at all. Used for the easy direction of [FG65] in paper
Remark 2.15, hence for the chordality claim of paper Remark 2.11 (`rem:fill-sanity`). Write
the cycle as an edge `{u, a}` followed by a path `p` from `a` back to `u` of length at least
three, and let `b` be its penultimate vertex. Then `{a, b}` is not the first edge `{u, a}`
(as `b ≠ u`), and on the path `p` an edge at its start `a` leads to the second vertex of `p`,
which differs from the penultimate vertex `b` because `p` has length at least three. -/
theorem peo_cycle_snd_penultimate_not_mem_edges {V : Type*} {H : SimpleGraph V} {u : V}
    {c : H.Walk u u} (hc : c.IsCycle) (hlen : 4 ≤ c.length) :
    s(c.snd, c.penultimate) ∉ c.edges := by
  cases c with
  | nil => exact absurd hc SimpleGraph.Walk.not_isCycle_nil
  | cons h p =>
    have hp := (SimpleGraph.Walk.cons_isCycle_iff p h).mp hc
    rw [SimpleGraph.Walk.length_cons] at hlen
    have hpnil : ¬ p.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      omega
    rw [SimpleGraph.Walk.snd_cons, SimpleGraph.Walk.penultimate_cons_of_not_nil _ _ hpnil,
      SimpleGraph.Walk.edges_cons]
    intro hmem
    rcases List.mem_cons.mp hmem with he | he
    · have hb : p.penultimate ≠ u := (SimpleGraph.Walk.adj_penultimate hpnil).ne
      rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact h.ne h1.symm
      · exact hb h2
    · have h1 : p.penultimate = p.snd := hp.1.eq_snd_of_mem_edges he
      have h2 : p.length - 1 = 1 :=
        hp.1.getVert_injOn (show p.length - 1 ≤ p.length by omega)
          (show 1 ≤ p.length by omega) h1
      omega



/-- A graph with a perfect elimination ordering is chordal: the easy direction of the
Fulkerson–Gross characterization [FG65] quoted in paper Remark 2.15, used for the chordality
claim of paper Remark 2.11 (`rem:fill-sanity`); chordal is paper Definition 2.14's "no induced
cycle of length at least 4" (`IsChordal`). Given an induced cycle of length at least four, rotate
it to start at the `σ`-earliest vertex `m` of its vertex set. The two cycle-neighbours of `m`
are later neighbours of `m` in `G`, hence adjacent by the PEO; that edge of the induced subgraph
is an edge of the cycle, which `peo_cycle_snd_penultimate_not_mem_edges` forbids. -/
theorem isChordal_of_isPerfectEliminationOrdering {G : SimpleGraph (Fin n)}
    {σ : List (Fin n)} (h : IsPerfectEliminationOrdering G σ) : IsChordal G := by
  intro s v c hc hedges hcover
  by_contra hlt
  have hlen : 4 ≤ c.length := by omega
  obtain ⟨l₁, m, t, hσeq, hms, hl₁⟩ :=
    peo_exists_first_mem s σ ⟨v.1, fill_mem_of_isOrdering h.1 v.1, v.2⟩
  have hearly : ∀ x ∈ s, x ≠ m → AfterIn σ m x := by
    intro x hxs hxm
    have hxσ : x ∈ l₁ ++ m :: t := hσeq ▸ fill_mem_of_isOrdering h.1 x
    rcases List.mem_append.mp hxσ with hx | hx
    · exact absurd hxs (hl₁ x hx)
    · rcases List.mem_cons.mp hx with hx | hx
      · exact absurd hx hxm
      · obtain ⟨l₂, l₃, ht⟩ := List.append_of_mem hx
        exact ⟨l₁, l₂, l₃, by simp [hσeq, ht]⟩
  obtain ⟨m', hm'c, hm'v⟩ := hcover hms
  have hc' : (c.rotate m' hm'c).IsCycle := hc.rotate hm'c
  have hlen' : 4 ≤ (c.rotate m' hm'c).length := by
    rw [SimpleGraph.Walk.length_rotate]
    exact hlen
  have hnil : ¬ (c.rotate m' hm'c).Nil := hc'.not_nil
  have ha : G.Adj m (c.rotate m' hm'c).snd.1 := by
    rw [← hm'v]
    exact SimpleGraph.Walk.adj_snd hnil
  have hb : G.Adj m (c.rotate m' hm'c).penultimate.1 := by
    rw [← hm'v]
    exact (SimpleGraph.Walk.adj_penultimate hnil).symm
  have hab : (c.rotate m' hm'c).snd ≠ (c.rotate m' hm'c).penultimate :=
    hc'.snd_ne_penultimate
  have hadj : G.Adj (c.rotate m' hm'c).snd.1 (c.rotate m' hm'c).penultimate.1 :=
    h.2 m ⟨ha, hearly _ (c.rotate m' hm'c).snd.2 ha.ne.symm⟩
      ⟨hb, hearly _ (c.rotate m' hm'c).penultimate.2 hb.ne.symm⟩
      (fun heq => hab (Subtype.ext heq))
  have hmem : s((c.rotate m' hm'c).snd, (c.rotate m' hm'c).penultimate) ∈ c.edges :=
    hedges _ ((SimpleGraph.mem_edgeSet _).mpr hadj)
  exact peo_cycle_snd_penultimate_not_mem_edges hc' hlen'
    ((SimpleGraph.Walk.rotate_edges c m' hm'c).mem_iff.mpr hmem)



/-- `G⁺_σ` is chordal (paper Remark 2.11, `rem:fill-sanity`; chordal as in paper
Definition 2.14): `σ` is a PEO of it (`fillGraph_isPerfectEliminationOrdering`), and a graph
with a PEO is chordal (`isChordal_of_isPerfectEliminationOrdering`, paper Remark 2.15). -/
theorem fillGraph_isChordal (A : Matrix (Fin n) (Fin n) ℝ) (σ : List (Fin n))
    (hσ : IsOrdering σ) : IsChordal (fillGraph A σ) :=
  isChordal_of_isPerfectEliminationOrdering (fillGraph_isPerfectEliminationOrdering A σ hσ)



/-- `Gᴸ_σ ⊆ G⁺_σ`: the factor side of the last claim of paper Remark 2.11 (`rem:fill-sanity`),
that `G⁺_σ` is exactly the symbolic pattern of `L + Lᵀ` (paper Definition 2.23). Symbolically,
the positions `{j, k}` of `L + Lᵀ` are committed at the predecessors of the earlier of `j, k`,
and the predicted ones are exactly the edges of `G⁺_σ`: `fillGraph` is read off at that
committing prefix (`fillGraph_adj_iff`) and agrees with the paper's cumulative graph
(`fillGraphGame_eq_fillGraph`). Numerically the factor pattern `Gᴸ_σ` (`factorPattern`, the
pattern of the assembled factor by `factorPattern_adj_iff_factorEntry`) can only lose
positions: factor adjacency is predicted nonzero (`numeric_le_symbolic`, paper
Definition 2.12), and equality holds iff `σ` is clean (`clean_iff_factor_pattern`). Both graphs
live on the whole vertex set `Fin n`, as the equality `Gᴸ_σ = G⁺_σ` of Conjecture 2.27
requires. -/
theorem factorPattern_le_fillGraph {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (σ : List (Fin n)) (hσ : IsOrdering σ) : factorPattern A σ ≤ fillGraph A σ := by
  intro j k h
  exact (numeric_le_symbolic hA).2 σ hσ j k h

end CholeskyCancellations

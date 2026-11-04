/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.TakeWhile
import Section_4_PositiveResults.F_PeelingAndCycles

/-! # A peelable vertex exists (paper Section 4)

Every suitable graph has a peelable vertex (`exists_peel_vertex`), the Dirac-style endpoint lemma behind the chordal peeling arguments.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as the Section 2 files; graph classes are predicates on `SimpleGraph (Fin n)` patterns and cleanliness is quantified per SPD realization through `PatternAdmitsPerMatrixCleanOrdering`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- **Peel vertex existence (one-triangle case).** In a chordal
graph whose unique triangle is `T`, inside any survivor set
`R ⊇ T` with `R \ T` nonempty there is a vertex of `R \ T` with at
most one neighbour in `R`: take a longest path in `R \ T`; the
master cycle exclusion bounds each endpoint's `(R \ T)`-neighbours
by its predecessor, and the two endpoints cannot both touch `T`
(that closes a cycle through `T`); the untouched endpoint works. A
singleton path has no `(R \ T)`-neighbours and at most one
`T`-neighbour (two would make a second triangle). -/
theorem exists_peel_vertex {G : SimpleGraph (Fin n)}
    {T R : Finset (Fin n)}
    (hG : IsChordal G)
    (huniq : ∀ T' : Finset (Fin n), T'.card = 3 →
      G.IsClique (↑T' : Set (Fin n)) → T' = T)
    (hTclq : G.IsClique (↑T : Set (Fin n)))
    (hne : (R \ T).Nonempty) :
    ∃ x ∈ R \ T, ∃ u : Fin n, ∀ y : Fin n, y ∈ R → y ≠ x →
      G.Adj x y → y = u := by
  classical
  set U := R \ T with hUdef
  have hUT : ∀ z ∈ U, z ∉ T := fun z hz => (Finset.mem_sdiff.mp hz).2
  have hTle1 : ∀ x : Fin n, x ∉ T → ∀ t₁ ∈ T, ∀ t₂ ∈ T,
      G.Adj x t₁ → G.Adj x t₂ → t₁ = t₂ := by
    intro x hxT t₁ ht₁ t₂ ht₂ h1 h2
    by_contra hne12
    have hnotmem : x ∉ ({t₁, t₂} : Finset (Fin n)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl)
      · exact hxT ht₁
      · exact hxT ht₂
    have hcard3 : (insert x {t₁, t₂} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem hnotmem,
        Finset.card_pair hne12]
    have hclq : G.IsClique (↑(insert x {t₁, t₂} : Finset (Fin n)) : Set (Fin n)) := by
      intro p hp r hr hpr
      rw [Finset.mem_coe] at hp hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp hr
      rcases hp with rfl | rfl | rfl <;>
        rcases hr with rfl | rfl | rfl
      · exact absurd rfl hpr
      · exact h1
      · exact h2
      · exact h1.symm
      · exact absurd rfl hpr
      · exact hTclq (Finset.mem_coe.mpr ht₁)
          (Finset.mem_coe.mpr ht₂) hne12
      · exact h2.symm
      · exact hTclq (Finset.mem_coe.mpr ht₂)
          (Finset.mem_coe.mpr ht₁) (Ne.symm hne12)
      · exact absurd rfl hpr
    have hT' := huniq _ hcard3 hclq
    have hxmem : x ∈ T := hT' ▸ Finset.mem_insert_self x {t₁, t₂}
    exact hxT hxmem
  obtain ⟨a, b, q, hq, hqU, hqmax⟩ := exists_longest_path_in (G := G) hne
  have haU : a ∈ U := hqU a q.start_mem_support
  have hbU : b ∈ U := hqU b q.end_mem_support
  have hnocycle : ∀ (w : Fin n) (c : G.Walk w w), c.IsCycle →
      ∀ z ∈ c.support, z ∉ U := by
    intro w c hc z hz hzU
    exact hUT z hzU (cycle_support_subset_T hG huniq c hc z hz)
  have hmaxb : ∀ x ∈ U, G.Adj b x → x ∈ q.support :=
    maximal_endpoint_mem q hq hqU
      (fun b' q' hq' hqU' => hqmax a b' q' hq' hqU')
  have hqUrev : ∀ z ∈ q.reverse.support, z ∈ U := by
    intro z hz
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    exact hqU z hz
  have hrevPath : ∀ {x y : Fin n} (w : G.Walk x y), w.IsPath →
      w.reverse.IsPath := by
    intro x y w hw
    apply SimpleGraph.Walk.IsPath.mk'
    rw [SimpleGraph.Walk.support_reverse]
    exact List.nodup_reverse.mpr hw.support_nodup
  have hmaxrev : ∀ (a'' : Fin n) (q'' : G.Walk b a''), q''.IsPath →
      (∀ z ∈ q''.support, z ∈ U) →
        q''.length ≤ q.reverse.length := by
    intro a'' q'' hq'' hq''U
    have h2 := hqmax a'' b q''.reverse
      (hrevPath q'' hq'')
      (by intro z hz
          rw [SimpleGraph.Walk.support_reverse,
            List.mem_reverse] at hz
          exact hq''U z hz)
    rw [SimpleGraph.Walk.length_reverse] at h2
    have h3 : q.reverse.length = q.length :=
      SimpleGraph.Walk.length_reverse q
    omega
  have hmaxa : ∀ x ∈ U, G.Adj a x → x ∈ q.reverse.support :=
    maximal_endpoint_mem q.reverse
      (hrevPath q hq) hqUrev hmaxrev
  have hendb := endpoint_neighbors_eq_pred q hq hqU hmaxb hnocycle
  have henda := endpoint_neighbors_eq_pred q.reverse
    (hrevPath q hq) hqUrev hmaxa hnocycle
  by_cases hlen0 : q.length = 0
  · have hab : a = b := by
      have h1 : q.getVert 0 = a := SimpleGraph.Walk.getVert_zero q
      have h2 : q.getVert q.length = b :=
        SimpleGraph.Walk.getVert_length q
      rw [hlen0] at h2
      exact h1.symm.trans h2
    have hnoU : ∀ x ∈ U, ¬ G.Adj a x := by
      intro x hxU hadj
      have hadj' : G.Adj b x := hab ▸ hadj
      have hx := hendb x hxU hadj'
      rw [hlen0] at hx
      have h0 : q.getVert (0 - 1) = a := by
        simp [SimpleGraph.Walk.getVert_zero]
      rw [h0] at hx
      exact (Ne.symm hadj.ne) hx
    by_cases hex : ∃ t ∈ T, G.Adj a t
    · obtain ⟨t₀, ht₀, hadj₀⟩ := hex
      refine ⟨a, haU, t₀, ?_⟩
      intro y hyR hya hadj
      by_cases hyT : y ∈ T
      · exact hTle1 a (hUT a haU) y hyT t₀ ht₀ hadj hadj₀
      · exact absurd hadj
          (hnoU y (Finset.mem_sdiff.mpr ⟨hyR, hyT⟩))
    · refine ⟨a, haU, a, ?_⟩
      intro y hyR hya hadj
      by_cases hyT : y ∈ T
      · exact absurd ⟨y, hyT, hadj⟩ hex
      · exact absurd hadj
          (hnoU y (Finset.mem_sdiff.mpr ⟨hyR, hyT⟩))
  · have hlen1 : 1 ≤ q.length := Nat.one_le_iff_ne_zero.mpr hlen0
    have hab : a ≠ b := by
      intro h
      subst h
      have h1 : q.getVert 0 = a := SimpleGraph.Walk.getVert_zero q
      have h2 : q.getVert q.length = a :=
        SimpleGraph.Walk.getVert_length q
      have heq := hq.getVert_injOn
        (Set.mem_Iic.mpr (by omega : 0 ≤ q.length))
        (Set.mem_Iic.mpr (by omega : q.length ≤ q.length))
        (h1.trans h2.symm)
      omega
    have hnotboth : ¬ ((∃ t ∈ T, G.Adj a t) ∧
        (∃ t ∈ T, G.Adj b t)) := by
      rintro ⟨⟨ta, htaT, hata⟩, ⟨tb, htbT, hbtb⟩⟩
      have htaP : ta ∉ q.support :=
        fun h => hUT ta (hqU ta h) htaT
      have htbP : tb ∉ q.support :=
        fun h => hUT tb (hqU tb h) htbT
      by_cases hteq : ta = tb
      · subst hteq
        have hneat : a ≠ ta :=
          fun h => hUT a haU (by rw [h]; exact htaT)
        have hcyc := isCycle_append_two_edges q hq hbtb hata.symm
          htaP (Ne.symm hab) hneat hlen1
        have hamem : a ∈ ((q.append
            (SimpleGraph.Walk.cons hbtb
              SimpleGraph.Walk.nil)).append
            (SimpleGraph.Walk.cons hata.symm
              SimpleGraph.Walk.nil)).support := by
          rw [SimpleGraph.Walk.mem_support_append_iff,
            SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inl (Or.inl q.start_mem_support)
        exact hnocycle a _ hcyc a hamem haU
      · set P' := SimpleGraph.Walk.cons hata.symm q with hP'def
        have hP' : P'.IsPath := by
          rw [hP'def]
          apply SimpleGraph.Walk.IsPath.mk'
          rw [SimpleGraph.Walk.support_cons]
          exact List.nodup_cons.mpr ⟨htaP, hq.support_nodup⟩
        have htbP' : tb ∉ P'.support := by
          rw [hP'def, SimpleGraph.Walk.support_cons]
          simp only [List.mem_cons]
          rintro (h | h)
          · exact hteq h.symm
          · exact htbP h
        have htbta : G.Adj tb ta :=
          hTclq (Finset.mem_coe.mpr htbT)
            (Finset.mem_coe.mpr htaT) (Ne.symm hteq)
        have hnebta : b ≠ ta :=
          fun h => hUT b hbU (by rw [h]; exact htaT)
        have hlenP' : 1 ≤ P'.length := by
          rw [hP'def, SimpleGraph.Walk.length_cons]
          omega
        have hcyc := isCycle_append_two_edges P' hP' hbtb htbta
          htbP' hnebta hteq hlenP'
        have haP' : a ∈ P'.support := by
          rw [hP'def, SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ q.start_mem_support
        have hamem : a ∈ ((P'.append
            (SimpleGraph.Walk.cons hbtb
              SimpleGraph.Walk.nil)).append
            (SimpleGraph.Walk.cons htbta
              SimpleGraph.Walk.nil)).support := by
          rw [SimpleGraph.Walk.mem_support_append_iff,
            SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inl (Or.inl haP')
        exact hnocycle ta _ hcyc a hamem haU
    by_cases hexb : ∃ t ∈ T, G.Adj b t
    · have hnoa : ∀ t ∈ T, ¬ G.Adj a t := fun t ht hadj =>
        hnotboth ⟨⟨t, ht, hadj⟩, hexb⟩
      refine ⟨a, haU,
        q.reverse.getVert (q.reverse.length - 1), ?_⟩
      intro y hyR hya hadj
      by_cases hyT : y ∈ T
      · exact absurd hadj (hnoa y hyT)
      · exact henda y (Finset.mem_sdiff.mpr ⟨hyR, hyT⟩) hadj
    · have hnob : ∀ t ∈ T, ¬ G.Adj b t := fun t ht hadj =>
        hexb ⟨t, ht, hadj⟩
      refine ⟨b, hbU, q.getVert (q.length - 1), ?_⟩
      intro y hyR hyb hadj
      by_cases hyT : y ∈ T
      · exact absurd hadj (hnob y hyT)
      · exact hendb y (Finset.mem_sdiff.mpr ⟨hyR, hyT⟩) hadj

end CholeskyCancellations

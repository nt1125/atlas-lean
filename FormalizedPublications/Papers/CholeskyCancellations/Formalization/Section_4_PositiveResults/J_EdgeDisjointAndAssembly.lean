/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.TakeWhile
import Section_4_PositiveResults.I_OneTriangleContinuation

/-! # Edge-disjoint triangles and assembly (paper Section 4)

Chordal states, the edge-disjoint continuation, the per-matrix edge-disjoint class theorem (`edge_disjoint_perMatrix`), and the assembly `positives` (paper Theorem 4.8).
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as the Section 2 files; graph classes are predicates on `SimpleGraph (Fin n)` patterns and cleanliness is quantified per SPD realization through `PatternAdmitsPerMatrixCleanOrdering`. (Plain comment: a docstring cannot precede `variable`.) -/
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



/-- With no survivors left, the empty continuation is clean. -/
theorem admitsCleanContinuation_of_survivors_empty
    {A : Matrix (Fin n) (Fin n) ℝ} {lS : List (Fin n)}
    {S : Finset (Fin n)} (henum : Enumerates lS S)
    (h : ∀ x : Fin n, x ∈ S) :
    AdmitsCleanContinuation A lS S := by
  refine ⟨henum, [], List.nodup_nil, ?_, ?_⟩
  · intro x
    exact ⟨fun hx => absurd hx List.not_mem_nil,
      fun hx => absurd (h x) hx⟩
  · intro p x hAfter _
    obtain ⟨l₁, l₂, l₃, hl⟩ := hAfter
    have hlen := congrArg List.length hl
    simp only [List.length_nil, List.length_append,
      List.length_cons] at hlen
    omega



/-- **Edge-disjoint triangles continuation.** From a chordal state
in a pattern with `ω ≤ 3` and pairwise edge-disjoint triangles
there is a clean continuation: peel the vertex supplied by
`exists_peel_vertex_iii` — a pendant vertex (clean, changing no
entry) or a clean apex of a leaf triangle (chosen by the exchange
step; the one updated pair stays a pattern edge with nonzero
entry) — and recurse. -/
theorem edge_disjoint_continuation {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    ∀ (m : ℕ) {lS : List (Fin n)} {S : Finset (Fin n)},
      (Finset.univ \ S).card ≤ m →
      IsChordal (patternGraph A) → (patternGraph A).cliqueNum ≤ 3 →
      TrianglesEdgeDisjoint (patternGraph A) →
      IsChordalState A lS S →
      AdmitsCleanContinuation A lS S := by
  intro m
  induction m with
  | zero =>
      intro lS S hcard hG hω hedge hstate
      have hempty : Finset.univ \ S = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      refine admitsCleanContinuation_of_survivors_empty hstate.1 ?_
      intro x
      by_contra hx
      have hx2 : x ∈ Finset.univ \ S :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
      rw [hempty] at hx2
      exact Finset.notMem_empty x hx2
  | succ m ih =>
      intro lS S hcard hG hω hedge hstate
      obtain ⟨henum, hgadj, hentry⟩ := hstate
      by_cases hne : (Finset.univ \ S).Nonempty
      · have hcardeq : ∀ v : Fin n, v ∉ S →
            (Finset.univ \ insert v S).card ≤ m := by
          intro v hv
          have heq : Finset.univ \ insert v S
              = (Finset.univ \ S).erase v := by
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_univ,
              Finset.mem_insert, Finset.mem_erase, true_and,
              not_or]
          rw [heq, Finset.card_erase_of_mem
            (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩)]
          omega
        rcases exists_peel_vertex_iii hG hω hedge
            (Finset.univ \ S) hne with hA' | hB
        · obtain ⟨v, hvR, u, hu⟩ := hA'
          have hv : v ∉ S := (Finset.mem_sdiff.mp hvR).2
          have hgame_of : ∀ x : Fin n, x ∉ S → x ≠ v →
              (gameGraph (patternGraph A) lS).Adj v x →
              (patternGraph A).Adj v x :=
            fun x hxS hxv h =>
              (hgadj v x hv hxS (Ne.symm hxv)).mp h
          obtain ⟨u', hN, hentry'⟩ :
              ∃ u' : Fin n, (∀ x : Fin n, x ∉ S → x ≠ v →
                  (gameGraph (patternGraph A) lS).Adj v x →
                    x = u') ∧
                schurEntry A S v u' ≠ 0 := by
            by_cases hex : ∃ y : Fin n,
                y ∈ Finset.univ \ S ∧ y ≠ v ∧
                (patternGraph A).Adj v y
            · obtain ⟨y₀, hy₀R, hy₀v, hAdj₀⟩ := hex
              have hy₀u : y₀ = u := hu y₀ hy₀R hy₀v hAdj₀
              have huS : u ∉ S :=
                hy₀u ▸ (Finset.mem_sdiff.mp hy₀R).2
              have huv : u ≠ v := hy₀u ▸ hy₀v
              have hAdjU : (patternGraph A).Adj v u := hy₀u ▸ hAdj₀
              refine ⟨u, ?_,
                (hentry v u hv huS (Ne.symm huv)).mpr hAdjU⟩
              intro x hxS hxv hgame
              exact hu x
                (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxS⟩)
                hxv (hgame_of x hxS hxv hgame)
            · refine ⟨v, ?_, ne_of_gt (schurEntry_pos hA S hv)⟩
              intro x hxS hxv hgame
              exact absurd ⟨x, Finset.mem_sdiff.mpr
                ⟨Finset.mem_univ x, hxS⟩, hxv,
                hgame_of x hxS hxv hgame⟩ hex
          obtain ⟨hclean, hent'', hgame''⟩ :=
            peel_singleton_neighbor hA henum hv hN hentry'
          refine admitsCleanContinuation_cons hv hclean ?_
          refine ih (hcardeq v hv) hG hω hedge ?_
          refine ⟨enumerates_append_singleton henum hv, ?_, ?_⟩
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
        · obtain ⟨c, a, d, hcR, haR, hdR, hca, hcd, had, hcad,
            hcbd, hadj, ha_bd, hd_bd⟩ := hB
          have hc : c ∉ S := (Finset.mem_sdiff.mp hcR).2
          have ha : a ∉ S := (Finset.mem_sdiff.mp haR).2
          have hd : d ∉ S := (Finset.mem_sdiff.mp hdR).2
          have eca : schurEntry A S c a ≠ 0 :=
            (hentry c a hc ha hca).mpr hcad
          have ecd : schurEntry A S c d ≠ 0 :=
            (hentry c d hc hd hcd).mpr hcbd
          have ead : schurEntry A S a d ≠ 0 :=
            (hentry a d ha hd had).mpr hadj
          have eac : schurEntry A S a c ≠ 0 := by
            rw [schurEntry_symm hA S a c]
            exact eca
          have edc : schurEntry A S d c ≠ 0 := by
            rw [schurEntry_symm hA S d c]
            exact ecd
          have eda : schurEntry A S d a ≠ 0 := by
            rw [schurEntry_symm hA S d a]
            exact ead
          have finish_pair : ∀ (v x₀ : Fin n), v ∉ S → x₀ ∉ S →
              v ≠ x₀ → v ≠ c → x₀ ≠ c →
              (∀ y : Fin n, y ∉ S → y ≠ v →
                (patternGraph A).Adj v y → y = c ∨ y = x₀) →
              (patternGraph A).Adj x₀ c →
              schurEntry A S v x₀ ≠ 0 → schurEntry A S v c ≠ 0 →
              schurEntry A (insert v S) x₀ c ≠ 0 →
              AdmitsCleanContinuation A lS S := by
            intro v x₀ hv hx₀ hvx hvc hxc hbds hadjxc hex hec
              hafter
            have hN : ∀ x : Fin n, x ∉ S → x ≠ v →
                (gameGraph (patternGraph A) lS).Adj v x →
                  x = x₀ ∨ x = c := by
              intro x hxS hxv hgame
              have hadjG : (patternGraph A).Adj v x :=
                (hgadj v x hv hxS (Ne.symm hxv)).mp hgame
              rcases hbds x hxS hxv hadjG with h | h
              · exact Or.inr h
              · exact Or.inl h
            obtain ⟨hclean, hent'', hgame''⟩ :=
              peel_clean_simplicial_pair hA henum hv hx₀ hc hvx
                hvc hxc hN ((hgadj x₀ c hx₀ hc hxc).mpr hadjxc)
                hex hec hafter
            refine admitsCleanContinuation_cons hv hclean ?_
            refine ih (hcardeq v hv) hG hω hedge ?_
            refine ⟨enumerates_append_singleton henum hv, ?_, ?_⟩
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
              by_cases hpair : SamePair x y x₀ c
              · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact ⟨fun _ => hadjxc, fun _ => hafter⟩
                · constructor
                  · intro _
                    exact hadjxc.symm
                  · intro _
                    rw [schurEntry_symm hA]
                    exact hafter
              · rw [hent'' x y hx hy hxy hpair]
                exact hentry x y hxS hyS hxy
          rcases exists_clean_apex hA ha hd hc had (Ne.symm hca)
            (Ne.symm hcd) eac with hp | hp
          · have h1 : d ∉ insert a S := by
              rw [Finset.mem_insert]
              push Not
              exact ⟨Ne.symm had, hd⟩
            have h2 : c ∉ insert a S := by
              rw [Finset.mem_insert]
              push Not
              exact ⟨hca, hc⟩
            have hafter : schurEntry A (insert a S) d c ≠ 0 := by
              rw [schur_quotient hA S a ha d c h1 h2]
              exact hp
            exact finish_pair a d ha hd had (Ne.symm hca)
              (Ne.symm hcd)
              (fun y hyS hyv hadjy => ha_bd y
                (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyS⟩)
                hyv hadjy)
              hcbd.symm ead eac hafter
          · have h1 : a ∉ insert d S := by
              rw [Finset.mem_insert]
              push Not
              exact ⟨had, ha⟩
            have h2 : c ∉ insert d S := by
              rw [Finset.mem_insert]
              push Not
              exact ⟨hcd, hc⟩
            have hafter : schurEntry A (insert d S) a c ≠ 0 := by
              rw [schur_quotient hA S d hd a c h1 h2]
              exact hp
            exact finish_pair d a hd ha (Ne.symm had)
              (Ne.symm hcd) (Ne.symm hca)
              (fun y hyS hyv hadjy => hd_bd y
                (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyS⟩)
                hyv hadjy)
              hcad.symm eda edc hafter
      · have hempty : Finset.univ \ S = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hne
        refine admitsCleanContinuation_of_survivors_empty henum ?_
        intro x
        by_contra hx
        have hx2 : x ∈ Finset.univ \ S :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
        rw [hempty] at hx2
        exact Finset.notMem_empty x hx2



/-- Chordal graphs with `ω ≤ 3` and pairwise edge-disjoint
triangles admit per-matrix clean orderings (paper Theorem 4.8
(iii), `thm:positives`, in its per-matrix form). -/
theorem edge_disjoint_perMatrix {G : SimpleGraph (Fin n)}
    (hG : IsChordal G) (hω : G.cliqueNum ≤ 3)
    (hedge : TrianglesEdgeDisjoint G) :
    PatternAdmitsPerMatrixCleanOrdering G := by
  intro A hA hpat
  apply exists_clean_of_continuation_empty hA
  refine edge_disjoint_continuation hA
    ((Finset.univ \ (∅ : Finset (Fin n))).card) le_rfl ?_ ?_ ?_
    ?_
  · rwa [hpat]
  · rwa [hpat]
  · rwa [hpat]
  · refine ⟨⟨by simp, by simp⟩, ?_, ?_⟩
    · intro x y _ _ _
      exact Iff.rfl
    · intro x y _ _ hxy
      rw [schurEntry_empty]
      constructor
      · intro hne0
        exact patternGraph_adj_of_entry hxy hne0
      · intro hadj
        exact patternGraph_adj_entry hA hadj




/-- Conjecture 1 holds for (i) 2-path strips and dominating-vertex
fans, (ii) chordal graphs with exactly one triangle, and
(iii) chordal graphs with `ω ≤ 3` and pairwise edge-disjoint
triangles (paper Theorem 4.8, `thm:positives`). Each class is
proved here in the per-matrix form — a clean ordering per
realization. Through paper Definition 2.25, Theorem 4.8 asserts
the stronger adaptive strategy form
(`PatternAdmitsAdaptiveStrategy`, one pivot-choice rule for all
realizations); that form is defined in
`E_StrategyVocabulary.lean` but is not proved here, and Remark
4.9's no-fixed-ordering witness is not formalized. What is proved
is therefore weaker than Theorem 4.8 in the paper's defined sense.
The parts are proved by
`strips_perMatrix` and `fans_perMatrix` (State 0/1 inductions
through `AdmitsCleanContinuation`),
`one_triangle_perMatrix` (peeling endpoints of longest paths off
the unique triangle), and `edge_disjoint_perMatrix` (Dirac
endpoint simpliciality plus leaf-triangle peeling). -/
theorem positives :
    (∀ {n : ℕ} (G : SimpleGraph (Fin n)), IsStripPattern G →
      PatternAdmitsPerMatrixCleanOrdering G)
    ∧ (∀ {n : ℕ} (G : SimpleGraph (Fin n)), IsFanPattern G →
        PatternAdmitsPerMatrixCleanOrdering G)
    ∧ (∀ {n : ℕ} (G : SimpleGraph (Fin n)),
        IsChordal G → ExactlyOneTriangle G → PatternAdmitsPerMatrixCleanOrdering G)
    ∧ (∀ {n : ℕ} (G : SimpleGraph (Fin n)),
        IsChordal G → G.cliqueNum ≤ 3 → TrianglesEdgeDisjoint G →
          PatternAdmitsPerMatrixCleanOrdering G) :=
  ⟨fun {n} G hG => @strips_perMatrix n G hG,
    fun {n} G hG => @fans_perMatrix n G hG,
    fun {n} G h1 h2 => @one_triangle_perMatrix n G h1 h2,
    fun {n} G h1 h2 h3 => @edge_disjoint_perMatrix n G h1 h2 h3⟩

end CholeskyCancellations

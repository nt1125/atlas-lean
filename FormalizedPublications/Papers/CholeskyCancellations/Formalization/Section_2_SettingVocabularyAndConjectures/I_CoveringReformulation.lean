/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Section_2_SettingVocabularyAndConjectures.H_BlockDiagonal

/-! # The covering reformulation (paper Section 2)

Paper Remark 2.30 (`rem:covering`): "Conjecture 2.27 fails for a pattern `G` exactly when some
blocking family is realizable for `G`: a matrix has no clean ordering iff its active slots spoil
every permutation." Statement by statement:

* `not_isCleanOrdering_iff_exists_active_spoils` is the single-ordering core: `σ` is not clean
  for `A` (paper Definition 2.24) iff some slot active for `A` (Definition 2.28) spoils `σ`
  (Definition 2.29). A failure of cleanliness at a pair `{j, k}` is the active spoiling slot
  `(prefixSet σ j k, j, k)`; conversely an active spoiling slot is a predicted-nonzero position
  that vanishes at its committing level.
* `no_clean_ordering_iff_active_slots_spoil` is the remark's "a matrix has no clean ordering iff
  its active slots spoil every permutation" (permutations of `V` are the orderings `σ` with
  `IsOrdering σ`).
* `covering_reformulation` is the remark's first sentence at a pattern `G`: some SPD matrix with
  pattern `G` has no clean ordering iff some blocking family is realizable for `G`. For
  connected `G` — the conjecture's irreducibility hypothesis, which depends on the pattern alone
  (`irreducible_iff_connected`) — the left side is exactly the failure of Conjecture 2.27 at the
  pattern `G`; `covering_not_fill_graph_conjecture_iff` packages this for `fill_graph_conjecture`
  itself. The backward direction is the one Section 5 exploits (to refute the conjecture for
  `G`, realize a blocking family); the forward direction, read contrapositively, says that
  refuting every blocking family for `G` proves the conjecture at `G`, which is what a positive
  result at a given order requires.
-/

open scoped Matrix

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): vertices `Fin n`, SPD = `Matrix.PosDef`,
levels `Finset (Fin n)`, pivot-order list orderings, Schur entries through `schurEntry` only.
(Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- One ordering is unclean exactly when an active slot spoils it (paper Remark 2.30,
`rem:covering`, for a single ordering; cleanliness is paper Definition 2.24, slots and activity
Definition 2.28, spoiling Definition 2.29). If cleanliness fails at a predicted-nonzero pair
`{j, k}`, the slot `(prefixSet σ j k, j, k)` — `j, k` survive their committing prefix by
`mem_prefixList_imp` — is active, and spoils `σ` because its level is the committing prefix and
the pair is game-adjacent there (`fillGraph_adj_iff`). Conversely an active slot spoiling `σ`
sits at the committing prefix of a predicted-nonzero pair (again `fillGraph_adj_iff`), where its
entry vanishes. No positive-definiteness is needed. -/
theorem not_isCleanOrdering_iff_exists_active_spoils (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : List (Fin n)) :
    ¬ IsCleanOrdering A σ ↔ ∃ s : Slot n, s.Active A ∧ s.Spoils A σ := by
  constructor
  · intro hnot
    have hex : ∃ j k : Fin n, PredictedNonzero A σ j k ∧
        schurEntry A (prefixSet σ j k) j k = 0 := by
      by_contra hno
      apply hnot
      intro j k hpred hzero
      exact hno ⟨j, k, hpred, hzero⟩
    obtain ⟨j, k, hpred, hzero⟩ := hex
    have hadj : (fillGraph A σ).Adj j k := hpred
    refine ⟨⟨prefixSet σ j k, j, k, ?_, ?_, hadj.ne⟩, hzero, rfl, ?_⟩
    · intro hj
      exact (mem_prefixList_imp (List.mem_toFinset.mp hj)).1 rfl
    · intro hk
      exact (mem_prefixList_imp (List.mem_toFinset.mp hk)).2 rfl
    · exact (fillGraph_adj_iff σ j k).mp hadj
  · rintro ⟨s, hact, hlevel, hgame⟩ hclean
    have hpred : PredictedNonzero A σ s.fst s.snd := (fillGraph_adj_iff σ s.fst s.snd).mpr hgame
    apply hclean s.fst s.snd hpred
    rw [← hlevel]
    exact hact



/-- A matrix has no clean ordering iff its active slots spoil every permutation (paper
Remark 2.30, `rem:covering`, second clause): `not_isCleanOrdering_iff_exists_active_spoils`
for every ordering `σ` of `V`. -/
theorem no_clean_ordering_iff_active_slots_spoil (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ σ : List (Fin n), IsOrdering σ → ¬ IsCleanOrdering A σ) ↔
      ∀ σ : List (Fin n), IsOrdering σ → ∃ s : Slot n, s.Active A ∧ s.Spoils A σ :=
  forall_congr' fun σ =>
    imp_congr_right fun _ => not_isCleanOrdering_iff_exists_active_spoils A σ



/-- Spoiling sees a matrix only through its pattern graph (paper Definition 2.29,
`def:blocking`: prediction is read in the symbolic graph `G_S` of the pattern), so matrices
with the same pattern are spoiled by the same slots; this is what lets the active slots of one
matrix form a blocking family for its pattern (paper Remark 2.30, `rem:covering`). -/
theorem covering_spoils_of_patternGraph_eq {A B : Matrix (Fin n) (Fin n) ℝ}
    (h : patternGraph A = patternGraph B) {s : Slot n} {σ : List (Fin n)}
    (hs : s.Spoils A σ) : s.Spoils B σ := by
  obtain ⟨hlevel, hgame⟩ := hs
  refine ⟨hlevel, ?_⟩
  rw [← h]
  exact hgame



/-- The covering reformulation (paper Remark 2.30, `rem:covering`): some SPD matrix with
pattern `G` has no clean ordering iff some blocking family is realizable for `G` (paper
Definition 2.29). For connected `G` (the conjecture's irreducibility, by
`irreducible_iff_connected`) the left side is the failure of Conjecture 2.27 at the pattern
`G`; see `covering_not_fill_graph_conjecture_iff`. Forward: the slots active for the bad matrix
`A` are realized by `A` itself, and they block `G` because for every ordering an active slot
spoils it (`not_isCleanOrdering_iff_exists_active_spoils`), whatever realization of `G`
spoiling is read against (`covering_spoils_of_patternGraph_eq`). Backward — the direction
Section 5 exploits: a matrix realizing a blocking family has an active spoiling slot for every
ordering, hence no clean ordering. Read contrapositively, the forward direction is the remark's
last sentence: refuting every blocking family for `G` proves the conjecture at `G`. -/
theorem covering_reformulation (G : SimpleGraph (Fin n)) :
    (∃ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef ∧ patternGraph A = G ∧
        ∀ σ : List (Fin n), IsOrdering σ → ¬ IsCleanOrdering A σ) ↔
      ∃ H : Set (Slot n), IsBlocking H G ∧ IsRealizable H G := by
  constructor
  · rintro ⟨A, hA, hG, hno⟩
    refine ⟨{s | s.Active A}, ?_, A, hA, hG, fun s hs => hs⟩
    intro B hB σ hσ
    obtain ⟨s, hact, hsp⟩ :=
      (not_isCleanOrdering_iff_exists_active_spoils A σ).mp (hno σ hσ)
    exact ⟨s, hact, covering_spoils_of_patternGraph_eq (hG.trans hB.symm) hsp⟩
  · rintro ⟨H, hblock, B, hB, hBG, hact⟩
    refine ⟨B, hB, hBG, fun σ hσ => ?_⟩
    obtain ⟨s, hsH, hsp⟩ := hblock B hBG σ hσ
    exact (not_isCleanOrdering_iff_exists_active_spoils B σ).mpr ⟨s, hact s hsH, hsp⟩



/-- Conjecture 2.27 fails exactly when, at some order, some blocking family is realizable for a
connected pattern (paper Remark 2.30, `rem:covering`, first sentence, stated for
`fill_graph_conjecture` itself). The conjecture's irreducibility hypothesis is connectedness of
the pattern (`irreducible_iff_connected`, with the symmetry of SPD matrices); order `0` is
harmless, since there the empty ordering is clean; and `covering_reformulation` does the rest. -/
theorem covering_not_fill_graph_conjecture_iff :
    ¬ fill_graph_conjecture ↔
      ∃ (m : ℕ) (G : SimpleGraph (Fin m)), G.Connected ∧
        ∃ H : Set (Slot m), IsBlocking H G ∧ IsRealizable H G := by
  constructor
  · intro hfail
    by_contra hno
    apply hfail
    intro m A hA hirr
    by_contra hnone
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        exact absurd ⟨[], ⟨List.nodup_nil, rfl⟩, fun j => j.elim0⟩ hnone
      · exact h0
    have hconn : (patternGraph A).Connected :=
      (irreducible_iff_connected hm (posDef_apply_comm hA)).mp hirr
    exact hno ⟨m, patternGraph A, hconn, (covering_reformulation (patternGraph A)).mp
      ⟨A, hA, rfl, fun σ hσ hcl => hnone ⟨σ, hσ, hcl⟩⟩⟩
  · rintro ⟨m, G, hG, H, hblock, hreal⟩ hconj
    obtain ⟨A, hA, hAG, hno⟩ := (covering_reformulation G).mpr ⟨H, hblock, hreal⟩
    obtain ⟨v⟩ := hG.nonempty
    have hirr : IsIrreducible A :=
      (irreducible_iff_connected v.pos (posDef_apply_comm hA)).mpr (hAG ▸ hG)
    obtain ⟨σ, hσ, hcl⟩ := hconj A hA hirr
    exact hno σ hσ hcl

end CholeskyCancellations

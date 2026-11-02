/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Section_5_EvenCounterexamplesAndOrderFour.C_ExistsCleanFour

/-! # Pairing Lemma (paper Section 5)

Fixed-point-free involutions, candidate slots, pairing configurations (paper Lemma 5.5), feasibility of candidate configurations, and forced magnitudes. Split from `Counterexamples.lean`.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as `Defs.lean`; concrete matrices are on `Fin 4` and `Fin (2 * m)` with pair/parity read from `Finset` levels and `Fin.val` division as in the paper's `P_k = {2k, 2k+1}` indexing. (Plain comment: a docstring cannot precede `variable`.) -/
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



theorem slotApexOf_spec {n : ℕ} (S W : Finset (Fin n)) (a0 : Fin n) {s : Slot n}
    (hcand : CandidateSlot S W s) :
    slotApexOf S W a0 s ∈ W ∧ s.level = insert (slotApexOf S W a0 s) S ∧
      s.fst ∈ W ∧ s.snd ∈ W ∧ s.fst ≠ slotApexOf S W a0 s ∧
      s.snd ≠ slotApexOf S W a0 s := by
  have hex := hcand.2
  unfold slotApexOf
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex



noncomputable def slotMissingOf {n : ℕ} (S W : Finset (Fin n)) (a0 : Fin n) (s : Slot n) : Fin n :=
  if h : ∃ d : Fin n, d ∈ W ∧ d ≠ slotApexOf S W a0 s ∧ d ≠ s.fst ∧ d ≠ s.snd then
    Classical.choose h else a0



theorem slotMissingOf_spec {n : ℕ} (S W : Finset (Fin n)) (a0 : Fin n) {s : Slot n}
    (hW : W.card = 4) (hcand : CandidateSlot S W s) :
    slotMissingOf S W a0 s ∈ W ∧ slotMissingOf S W a0 s ≠ slotApexOf S W a0 s ∧
      slotMissingOf S W a0 s ≠ s.fst ∧ slotMissingOf S W a0 s ≠ s.snd := by
  classical
  obtain ⟨haW, _hlevel, hfW, hsW, hfa, hsa⟩ := slotApexOf_spec S W a0 hcand
  have hex : ∃ d : Fin n, d ∈ W ∧ d ≠ slotApexOf S W a0 s ∧ d ≠ s.fst ∧ d ≠ s.snd := by
    set Q : Finset (Fin n) := {slotApexOf S W a0 s, s.fst, s.snd} with hQ
    have hQcard : Q.card = 3 := by
      rw [hQ, Finset.card_eq_three]
      exact ⟨slotApexOf S W a0 s, s.fst, s.snd,
        fun h => hfa h.symm, fun h => hsa h.symm, s.hne, rfl⟩
    obtain ⟨d, hdW, hdQ⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : Q.card < W.card)
    refine ⟨d, hdW, ?_, ?_, ?_⟩ <;> intro h <;> apply hdQ <;> simp [hQ, h]
  unfold slotMissingOf
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex



theorem slot_pair_eq_erase {n : ℕ} {W : Finset (Fin n)} (hW : W.card = 4)
    {u x y d : Fin n} (hu : u ∈ W) (hx : x ∈ W) (hy : y ∈ W) (hd : d ∈ W)
    (hux : u ≠ x) (huy : u ≠ y) (hud : u ≠ d) (hxy : x ≠ y)
    (hxd : x ≠ d) (hyd : y ≠ d) :
    ({x, y} : Finset (Fin n)) = (W.erase u).erase d := by
  have hQ : ({u, x, y, d} : Finset (Fin n)) = W := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact hu
      · exact hx
      · exact hy
      · exact hd
    · have hQcard : ({u, x, y, d} : Finset (Fin n)).card = 4 :=
        (Finset.card_eq_four).mpr ⟨u, x, y, d, hux, huy, hud, hxy, hxd, hyd, rfl⟩
      rw [hW, hQcard]
  ext z
  rw [← hQ]
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨hxd, hux.symm, Or.inr (Or.inl rfl)⟩
    · exact ⟨hyd, huy.symm, Or.inr (Or.inr (Or.inl rfl))⟩
  · rintro ⟨hzd, hzu, rfl | rfl | rfl | rfl⟩
    · exact absurd rfl hzu
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hzd



theorem slot_eq_of_fields {n : ℕ} {s t : Slot n}
    (hl : s.level = t.level) (hf : s.fst = t.fst) (hs : s.snd = t.snd) : s = t := by
  cases s
  cases t
  simp_all



/-- Auxiliary injectivity step for the Pairing Lemma: the missing
fourth vertex of a feasible candidate slot is injective on a feasible
family, by the exchange inequality for the additive system. -/
theorem candidate_feasible_missing_injOn (S W : Finset (Fin n)) (a0 : Fin n)
    (hW : W.card = 4) (H : Set (Slot n))
    (hCand : ∀ s ∈ H, CandidateSlot S W s)
    (hFeas : IsFeasibleAt H S) : Set.InjOn (slotMissingOf S W a0) H := by
  classical
  obtain ⟨τ, htpos, htsymm, hslots⟩ := hFeas
  have hEq : ∀ s ∈ H, τ s.fst s.snd
      = τ (slotApexOf S W a0 s) s.fst + τ (slotApexOf S W a0 s) s.snd := by
    intro s hs
    obtain ⟨_haW, hlevel, _, _, _, _⟩ :=
      slotApexOf_spec S W a0 (hCand s hs)
    obtain ⟨v, hlevelv, hvS, heq⟩ := hslots s hs
    have hva : v = slotApexOf S W a0 s := by
      have hvmem : v ∈ insert (slotApexOf S W a0 s) S := by
        rw [← hlevel, hlevelv]
        exact Finset.mem_insert_self v S
      rcases Finset.mem_insert.mp hvmem with h | h
      · exact h
      · exact absurd h hvS
    rwa [hva] at heq
  have hPair : ∀ s ∈ H, ({s.fst, s.snd} : Finset (Fin n))
      = (W.erase (slotApexOf S W a0 s)).erase (slotMissingOf S W a0 s) := by
    intro s hs
    obtain ⟨haW, _hlevel, hfW, hsW, hfa, hsa⟩ := slotApexOf_spec S W a0 (hCand s hs)
    obtain ⟨hmW, hma, hmf, hms⟩ := slotMissingOf_spec S W a0 hW (hCand s hs)
    exact slot_pair_eq_erase hW haW hfW hsW hmW
      (fun h => hfa h.symm) (fun h => hsa h.symm) (fun h => hma h.symm)
      s.hne (fun h => hmf h.symm) (fun h => hms h.symm)
  have hEq_of_pair : ∀ {s : Slot n}, s ∈ H → ∀ {x y : Fin n},
      ({s.fst, s.snd} : Finset (Fin n)) = {x, y} →
        τ x y = τ (slotApexOf S W a0 s) x + τ (slotApexOf S W a0 s) y := by
    intro s hs x y hpair
    have hraw := hEq s hs
    have hfst_mem : s.fst ∈ ({x, y} : Finset (Fin n)) := by
      rw [← hpair]; simp
    have hsnd_mem : s.snd ∈ ({x, y} : Finset (Fin n)) := by
      rw [← hpair]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfst_mem hsnd_mem
    rcases hfst_mem with hf | hf
    · have hsn : s.snd = y := by
        rcases hsnd_mem with h | h
        · exact absurd (hf.trans h.symm) s.hne
        · exact h
      rw [hf, hsn] at hraw
      exact hraw
    · have hsn : s.snd = x := by
        rcases hsnd_mem with h | h
        · exact h
        · exact absurd (hf.trans h.symm) s.hne
      rw [hf, hsn] at hraw
      rw [htsymm y x] at hraw
      linarith [hraw]
  intro s hs t ht hmiss
  obtain ⟨haW, hlevel, hfW, hsW, hfa, hsa⟩ := slotApexOf_spec S W a0 (hCand s hs)
  obtain ⟨haW', hlevel', hfW', hsW', hfa', hsa'⟩ := slotApexOf_spec S W a0 (hCand t ht)
  obtain ⟨hmW, hma, hmf, hms⟩ := slotMissingOf_spec S W a0 hW (hCand s hs)
  obtain ⟨hmW', hma', hmf', hms'⟩ := slotMissingOf_spec S W a0 hW (hCand t ht)
  by_cases hap : slotApexOf S W a0 s = slotApexOf S W a0 t
  · apply slot_eq_of_fields
    · rw [hlevel, hlevel', hap]
    · have hpair : ({s.fst, s.snd} : Finset (Fin n)) = {t.fst, t.snd} := by
        rw [hPair s hs, hPair t ht, hap, hmiss]
      have hm1 : s.fst ∈ ({t.fst, t.snd} : Finset (Fin n)) := by
        rw [← hpair]; simp
      have hm2 : s.snd ∈ ({t.fst, t.snd} : Finset (Fin n)) := by
        rw [← hpair]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
      rcases hm1 with h | h
      · exact h
      · rcases hm2 with h2 | h2
        · exfalso
          have hor_s := (hCand s hs).1
          have hor_t := (hCand t ht).1
          rw [h, h2] at hor_s
          exact lt_irrefl _ (hor_s.trans hor_t)
        · exact absurd (h.trans h2.symm) s.hne
    · have hpair : ({s.fst, s.snd} : Finset (Fin n)) = {t.fst, t.snd} := by
        rw [hPair s hs, hPair t ht, hap, hmiss]
      have hfst : s.fst = t.fst := by
        have hm1 : s.fst ∈ ({t.fst, t.snd} : Finset (Fin n)) := by
          rw [← hpair]; simp
        have hm2 : s.snd ∈ ({t.fst, t.snd} : Finset (Fin n)) := by
          rw [← hpair]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
        rcases hm1 with h | h
        · exact h
        · rcases hm2 with h2 | h2
          · exfalso
            have hor_s := (hCand s hs).1
            have hor_t := (hCand t ht).1
            rw [h, h2] at hor_s
            exact lt_irrefl _ (hor_s.trans hor_t)
          · exact absurd (h.trans h2.symm) s.hne
      have hm : t.snd ∈ ({s.fst, s.snd} : Finset (Fin n)) := by
        rw [hpair]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h
      · exfalso
        exact absurd (h.trans hfst).symm t.hne
      · exact h.symm
  · exfalso
    -- the missing-coordinate exchange contradiction
    have hu'_mem : slotApexOf S W a0 t ∈ ({s.fst, s.snd} : Finset (Fin n)) := by
      rw [hPair s hs]
      apply Finset.mem_erase.mpr
      constructor
      · intro h
        apply hma'
        rw [← hmiss]
        exact h.symm
      · exact Finset.mem_erase.mpr ⟨fun h => hap h.symm, haW'⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu'_mem
    -- choose the other element r of s's pair
    obtain ⟨r, hrpair, hr_ne_u', hrW, hr_ne_u, hr_ne_d⟩ :
        ∃ r, ({s.fst, s.snd} : Finset (Fin n)) = {slotApexOf S W a0 t, r} ∧
          r ≠ slotApexOf S W a0 t ∧ r ∈ W ∧ r ≠ slotApexOf S W a0 s ∧
          r ≠ slotMissingOf S W a0 s := by
      rcases hu'_mem with h | h
      · refine ⟨s.snd, ?_, fun hr => s.hne (h.symm.trans hr.symm), hsW, hsa, fun h => hms h.symm⟩
        rw [h]
      · refine ⟨s.fst, ?_, fun hr => s.hne (hr.trans h), hfW, hfa, fun h => hmf h.symm⟩
        rw [h, Finset.pair_comm]
    have hrpair_t : ({t.fst, t.snd} : Finset (Fin n))
        = {slotApexOf S W a0 s, r} := by
      rw [hPair t ht]
      have hpairerase := slot_pair_eq_erase (W := W) hW haW' haW hrW hmW
        (fun h => hap h.symm) (fun h => hr_ne_u' h.symm)
        (fun h => hma' (hmiss.symm.trans h.symm))
        (fun h => hr_ne_u h.symm) (fun h => hma h.symm) hr_ne_d
      rw [hmiss] at hpairerase
      exact hpairerase.symm
    have eqs : τ (slotApexOf S W a0 t) r
        = τ (slotApexOf S W a0 s) (slotApexOf S W a0 t)
          + τ (slotApexOf S W a0 s) r := hEq_of_pair hs hrpair
    have eqt : τ (slotApexOf S W a0 s) r
        = τ (slotApexOf S W a0 t) (slotApexOf S W a0 s)
          + τ (slotApexOf S W a0 t) r := hEq_of_pair ht hrpair_t
    rw [htsymm (slotApexOf S W a0 t) (slotApexOf S W a0 s)] at eqt
    have hpos := htpos (slotApexOf S W a0 s) (slotApexOf S W a0 t)
    linarith



/-- Auxiliary counting step for the Pairing Lemma: a feasible
candidate family has at most four slots. -/
theorem candidate_feasible_ncard_le_four (S W : Finset (Fin n))
    (hW : W.card = 4) (H : Set (Slot n))
    (hCand : ∀ s ∈ H, CandidateSlot S W s)
    (hFeas : IsFeasibleAt H S) : H.ncard ≤ 4 := by
  classical
  obtain ⟨a, b, c, e, -, -, -, -, -, -, _hWlab⟩ := Finset.card_eq_four.mp hW
  calc H.ncard ≤ (W : Set (Fin n)).ncard :=
        Set.ncard_le_ncard_of_injOn (slotMissingOf S W a)
          (fun s hs => (slotMissingOf_spec S W a hW (hCand s hs)).1)
          (candidate_feasible_missing_injOn S W a hW H hCand hFeas)
    _ = 4 := by rw [Set.ncard_coe_finset, hW]



/-- Auxiliary classification step for the Pairing Lemma: a feasible
four-slot candidate family using every apex is a pairing
configuration. The apex and missing-vertex maps are injective, hence
define a fixed-point-free permutation of `W`; a four-cycle is ruled
out by summing its four additive relations. -/
theorem pairingConfig_of_candidate_feasible_card_four (S W : Finset (Fin n))
    (hW : W.card = 4) (hWS : ∀ u ∈ W, u ∉ S) (H : Set (Slot n))
    (hCand : ∀ s ∈ H, CandidateSlot S W s)
    (hFeas : IsFeasibleAt H S) (hcard : H.ncard = 4)
    (hall : ∀ u ∈ W, ∃ s ∈ H, s.level = insert u S) :
    ∃ π : Fin n → Fin n, PairingConfig π S W H := by
  classical
  obtain ⟨a, -, -, -, -, -, -, -, -, -, -⟩ := Finset.card_eq_four.mp hW
  have hmissing_inj : Set.InjOn (slotMissingOf S W a) H :=
    candidate_feasible_missing_injOn S W a hW H hCand hFeas
  obtain ⟨τ, htpos, htsymm, hslots⟩ := hFeas
  have hEq : ∀ s ∈ H, τ s.fst s.snd
      = τ (slotApexOf S W a s) s.fst + τ (slotApexOf S W a s) s.snd := by
    intro s hs
    obtain ⟨_haW, hlevel, _, _, _, _⟩ := slotApexOf_spec S W a (hCand s hs)
    obtain ⟨v, hlevelv, hvS, heq⟩ := hslots s hs
    have hva : v = slotApexOf S W a s := by
      have hvmem : v ∈ insert (slotApexOf S W a s) S := by
        rw [← hlevel, hlevelv]
        exact Finset.mem_insert_self v S
      rcases Finset.mem_insert.mp hvmem with h | h
      · exact h
      · exact absurd h hvS
    rwa [hva] at heq
  have hPair : ∀ s ∈ H, ({s.fst, s.snd} : Finset (Fin n))
      = (W.erase (slotApexOf S W a s)).erase (slotMissingOf S W a s) := by
    intro s hs
    obtain ⟨haW, _hlevel, hfW, hsW, hfa, hsa⟩ := slotApexOf_spec S W a (hCand s hs)
    obtain ⟨hmW, hma, hmf, hms⟩ := slotMissingOf_spec S W a hW (hCand s hs)
    exact slot_pair_eq_erase hW haW hfW hsW hmW
      (fun h => hfa h.symm) (fun h => hsa h.symm) (fun h => hma h.symm)
      s.hne (fun h => hmf h.symm) (fun h => hms h.symm)
  have hEq_of_pair : ∀ {s : Slot n}, s ∈ H → ∀ {x y : Fin n},
      ({s.fst, s.snd} : Finset (Fin n)) = {x, y} →
        τ x y = τ (slotApexOf S W a s) x + τ (slotApexOf S W a s) y := by
    intro s hs x y hpair
    have hraw := hEq s hs
    have hfst_mem : s.fst ∈ ({x, y} : Finset (Fin n)) := by
      rw [← hpair]; simp
    have hsnd_mem : s.snd ∈ ({x, y} : Finset (Fin n)) := by
      rw [← hpair]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfst_mem hsnd_mem
    rcases hfst_mem with hf | hf
    · have hsn : s.snd = y := by
        rcases hsnd_mem with h | h
        · exact absurd (hf.trans h.symm) s.hne
        · exact h
      rw [hf, hsn] at hraw
      exact hraw
    · have hsn : s.snd = x := by
        rcases hsnd_mem with h | h
        · exact h
        · exact absurd (hf.trans h.symm) s.hne
      rw [hf, hsn] at hraw
      rw [htsymm y x] at hraw
      linarith [hraw]
  have hHfin : H.Finite := by
    apply Set.Finite.of_finite_image _ hmissing_inj
    apply Set.Finite.subset (Finset.finite_toSet W)
    rintro y ⟨s, hs, rfl⟩
    exact (slotMissingOf_spec S W a hW (hCand s hs)).1
  have hapex_maps : ∀ s ∈ H, slotApexOf S W a s ∈ (W : Set (Fin n)) := by
    intro s hs
    exact (slotApexOf_spec S W a (hCand s hs)).1
  have hapex_surj : Set.SurjOn (slotApexOf S W a) H (W : Set (Fin n)) := by
    intro u hu
    obtain ⟨s, hs, hlevel⟩ := hall u hu
    refine ⟨s, hs, ?_⟩
    obtain ⟨haW, hlevel_a, -, -, -, -⟩ := slotApexOf_spec S W a (hCand s hs)
    have humem : u ∈ insert (slotApexOf S W a s) S := by
      rw [← hlevel_a, hlevel]
      exact Finset.mem_insert_self u S
    rcases Finset.mem_insert.mp humem with h | h
    · exact h.symm
    · exact absurd h (hWS u hu)
  have hapex_image : slotApexOf S W a '' H = (W : Set (Fin n)) :=
    Set.Subset.antisymm
      (Set.MapsTo.image_subset (fun s hs => hapex_maps s hs)) hapex_surj
  have hapex_inj : Set.InjOn (slotApexOf S W a) H := by
    apply Set.injOn_of_ncard_image_eq _ hHfin
    rw [hapex_image, Set.ncard_coe_finset, hW, hcard]
  have hslotOf : ∀ u ∈ W, ∃ s ∈ H, slotApexOf S W a s = u := by
    intro u hu
    have hmem := hapex_surj hu
    obtain ⟨s, hs, hsu⟩ := hmem
    exact ⟨s, hs, hsu⟩
  set π : Fin n → Fin n := fun u => if h : u ∈ W then
    slotMissingOf S W a (Classical.choose (hslotOf u h)) else u with hπdef
  have hpi_spec : ∀ u ∈ W, ∃ s ∈ H, slotApexOf S W a s = u ∧
      slotMissingOf S W a s = π u := by
    intro u hu
    refine ⟨Classical.choose (hslotOf u hu),
      (Classical.choose_spec (hslotOf u hu)).1,
      (Classical.choose_spec (hslotOf u hu)).2, ?_⟩
    rw [hπdef]
    simp only [dite_eq_left hu]
  have hpi_mem : ∀ u ∈ W, π u ∈ W := by
    intro u hu
    obtain ⟨s, hs, _hap, hmiss⟩ := hpi_spec u hu
    rw [← hmiss]
    exact (slotMissingOf_spec S W a hW (hCand s hs)).1
  have hpi_ne : ∀ u ∈ W, π u ≠ u := by
    intro u hu
    obtain ⟨s, hs, hap, hmiss⟩ := hpi_spec u hu
    rw [← hmiss, ← hap]
    exact (slotMissingOf_spec S W a hW (hCand s hs)).2.1
  have hpi_inj : ∀ u ∈ W, ∀ v ∈ W, π u = π v → u = v := by
    intro u hu v hv huv
    obtain ⟨su, hsu, hapu, hmissu⟩ := hpi_spec u hu
    obtain ⟨sv, hsv, hapv, hmissv⟩ := hpi_spec v hv
    have hslot_eq : su = sv :=
      hmissing_inj hsu hsv (by rw [hmissu, hmissv, huv])
    rw [← hapu, ← hapv, hslot_eq]
  have hslot_unique : ∀ s ∈ H, π (slotApexOf S W a s) = slotMissingOf S W a s := by
    intro s hs
    set u := slotApexOf S W a s with hu_def
    have huW : u ∈ W := hapex_maps s hs
    obtain ⟨su, hsu, hapu, hmissu⟩ := hpi_spec u huW
    have hslot_eq : su = s := hapex_inj hsu hs (by rw [hapu, hu_def])
    rw [← hmissu, hslot_eq]
  have hW_of_four : ∀ {w x y z : Fin n}, w ∈ W → x ∈ W → y ∈ W → z ∈ W →
      w ≠ x → w ≠ y → w ≠ z → x ≠ y → x ≠ z → y ≠ z →
        W = {w, x, y, z} := by
    intro w x y z hw hx hy hz hwx hwy hwz hxy hxz hyz
    have hsub : ({w, x, y, z} : Finset (Fin n)) ⊆ W := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact hw
      · exact hx
      · exact hy
      · exact hz
    have hQcard : ({w, x, y, z} : Finset (Fin n)).card = 4 := by
      rw [Finset.card_eq_four]
      exact ⟨w, x, y, z, hwx, hwy, hwz, hxy, hxz, hyz, rfl⟩
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hW, hQcard])).symm
  have hpi_invol : ∀ u ∈ W, π (π u) = u := by
    intro u hu
    by_contra hnot
    set b := π u with hb_def
    set c := π b with hc_def
    have hbW : b ∈ W := hpi_mem u hu
    have hcW : c ∈ W := hpi_mem b hbW
    have hub : u ≠ b := fun h => hpi_ne u hu h.symm
    have hbc : b ≠ c := by
      have h := hpi_ne b hbW
      rw [← hc_def] at h
      exact h.symm
    have huc : u ≠ c := fun h => hnot h.symm
    obtain ⟨d, hdW, hdu, hdb, hdc⟩ :
        ∃ d, d ∈ W ∧ d ≠ u ∧ d ≠ b ∧ d ≠ c := by
      set Q : Finset (Fin n) := {u, b, c} with hQ
      have hQcard : Q.card = 3 := by
        rw [hQ, Finset.card_eq_three]
        exact ⟨u, b, c, hub, huc, hbc, rfl⟩
      obtain ⟨d, hdW, hdQ⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card (by omega : Q.card < W.card)
      refine ⟨d, hdW, ?_, ?_, ?_⟩ <;> intro h <;> apply hdQ <;> simp [hQ, h]
    have hW4 : W = {u, b, c, d} :=
      hW_of_four hu hbW hcW hdW hub huc (fun h => hdu h.symm) hbc
        (fun h => hdb h.symm) (fun h => hdc h.symm)
    have hpic : π c = d := by
      have hmem : π c ∈ W := hpi_mem c hcW
      rw [hW4] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h | h
      · exfalso
        have hdmem : π d ∈ W := hpi_mem d hdW
        rw [hW4] at hdmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hdmem
        rcases hdmem with hd' | hd' | hd' | hd'
        · exact absurd (hpi_inj d hdW c hcW (by rw [hd', h])) hdc
        · exact absurd (hpi_inj d hdW u hu (by rw [hd', hb_def])) hdu
        · exact absurd (hpi_inj d hdW b hbW (by rw [hd', hc_def])) hdb
        · exact hpi_ne d hdW hd'
      · exfalso
        have : c = u := hpi_inj c hcW u hu (by rw [h, hb_def])
        exact huc this.symm
      · exact absurd h (hpi_ne c hcW)
      · exact h
    have hpid : π d = u := by
      have hmem : π d ∈ W := hpi_mem d hdW
      rw [hW4] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h | h
      · exact h
      · exfalso
        exact absurd (hpi_inj d hdW u hu (by rw [h, hb_def])) hdu
      · exfalso
        exact absurd (hpi_inj d hdW b hbW (by rw [h, hc_def])) hdb
      · exact absurd h (hpi_ne d hdW)
    obtain ⟨su, hsu, hapu, hmissu⟩ := hpi_spec u hu
    obtain ⟨sb, hsb, hapb, hmissb⟩ := hpi_spec b hbW
    obtain ⟨sc, hsc, hapc, hmissc⟩ := hpi_spec c hcW
    obtain ⟨sd, hsd, hapd, hmissd⟩ := hpi_spec d hdW
    have pair_u : ({su.fst, su.snd} : Finset (Fin n)) = {c, d} := by
      have h := slot_pair_eq_erase hW hu hcW hdW hbW huc
        (fun h => hdu h.symm) hub (fun h => hdc h.symm) (fun h => hbc h.symm) hdb
      rw [hPair su hsu, hapu, hmissu] 
      exact h.symm
    have pair_b : ({sb.fst, sb.snd} : Finset (Fin n)) = {u, d} := by
      have h := slot_pair_eq_erase hW hbW hu hdW hcW (fun h => hub h.symm)
        (fun h => hdb h.symm) hbc (fun h => hdu h.symm) huc hdc
      rw [hPair sb hsb, hapb, hmissb]
      exact h.symm
    have pair_c : ({sc.fst, sc.snd} : Finset (Fin n)) = {u, b} := by
      have h := slot_pair_eq_erase hW hcW hu hbW hdW (fun h => huc h.symm)
        (fun h => hbc h.symm) (fun h => hdc h.symm) hub (fun h => hdu h.symm)
        (fun h => hdb h.symm)
      rw [hPair sc hsc, hapc, hmissc, hpic]
      exact h.symm
    have pair_d : ({sd.fst, sd.snd} : Finset (Fin n)) = {b, c} := by
      have h := slot_pair_eq_erase hW hdW hbW hcW hu hdb hdc hdu hbc
        (fun h => hub h.symm) (fun h => huc h.symm)
      rw [hPair sd hsd, hapd, hmissd, hpid]
      exact h.symm
    have eq_u : τ c d = τ u c + τ u d := by
      have h := hEq_of_pair hsu pair_u
      rwa [hapu] at h
    have eq_b : τ u d = τ b u + τ b d := by
      have h := hEq_of_pair hsb pair_b
      rwa [hapb] at h
    have eq_c : τ u b = τ c u + τ c b := by
      have h := hEq_of_pair hsc pair_c
      rwa [hapc] at h
    have eq_d : τ b c = τ d b + τ d c := by
      have h := hEq_of_pair hsd pair_d
      rwa [hapd] at h
    rw [htsymm b u] at eq_b
    rw [htsymm c u, htsymm c b] at eq_c
    rw [htsymm d b, htsymm d c] at eq_d
    have hp1 := htpos u c
    have hp2 := htpos b d
    linarith
  refine ⟨π, ?_, ?_, ?_⟩
  · intro u hu
    exact ⟨hpi_mem u hu, hpi_invol u hu, hpi_ne u hu⟩
  · intro u hu
    obtain ⟨s, hs, hap, hmiss⟩ := hpi_spec u hu
    refine ⟨s, hs, ?_, ?_⟩
    · have hlevel := (slotApexOf_spec S W a (hCand s hs)).2.1
      rwa [hap] at hlevel
    · rw [hPair s hs, hap, hmiss]
  · intro s hs
    refine ⟨slotApexOf S W a s, (slotApexOf_spec S W a (hCand s hs)).1,
      (slotApexOf_spec S W a (hCand s hs)).2.1, ?_⟩
    rw [hPair s hs, ← hslot_unique s hs]



/-- Auxiliary feasibility step for the Pairing Lemma: every pairing
configuration is feasible, with within-pair log-magnitude `2` and
all other log-magnitudes `1`. -/
theorem isFeasibleAt_of_pairingConfig (S W : Finset (Fin n))
    (hWS : ∀ u ∈ W, u ∉ S) (π : Fin n → Fin n) (H : Set (Slot n))
    (hcfg : PairingConfig π S W H) : IsFeasibleAt H S := by
  classical
  obtain ⟨hpi, _hexists, hexact⟩ := hcfg
  refine ⟨fun x y => if x ∈ W ∧ y ∈ W ∧ π x = y then 2 else 1, ?_, ?_, ?_⟩
  · intro j k
    by_cases h : j ∈ W ∧ k ∈ W ∧ π j = k <;> simp [h]
  · intro x y
    by_cases hx : x ∈ W <;> by_cases hy : y ∈ W
    · by_cases hxy : π x = y
      · have hyx : π y = x := by
          have hinv := (hpi x hx).2.1
          rw [hxy] at hinv
          exact hinv
        simp [hx, hy, hxy, hyx]
      · have hyx : π y ≠ x := by
          intro h
          apply hxy
          have hinv := (hpi y hy).2.1
          rw [h] at hinv
          exact hinv
        simp [hx, hy, hxy, hyx]
    · simp [hx, hy]
    · simp [hx, hy]
    · simp [hx, hy]
  · intro s hs
    obtain ⟨u, huW, hlevel, hpair⟩ := hexact s hs
    refine ⟨u, hlevel, hWS u huW, ?_⟩
    have hfst_pair : s.fst ∈ ({s.fst, s.snd} : Finset (Fin n)) := by simp
    have hsnd_pair : s.snd ∈ ({s.fst, s.snd} : Finset (Fin n)) := by simp
    rw [hpair] at hfst_pair hsnd_pair
    have hfstW : s.fst ∈ W :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hfst_pair)
    have hsndW : s.snd ∈ W :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hsnd_pair)
    have hfst_ne_u : s.fst ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hfst_pair)).1
    have hsnd_ne_u : s.snd ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hsnd_pair)).1
    have hfst_ne_piu : s.fst ≠ π u := (Finset.mem_erase.mp hfst_pair).1
    have hsnd_ne_piu : s.snd ≠ π u := (Finset.mem_erase.mp hsnd_pair).1
    have hpartner : π s.fst = s.snd := by
      have hpfW : π s.fst ∈ W := (hpi s.fst hfstW).1
      have hpf_ne_fst : π s.fst ≠ s.fst := (hpi s.fst hfstW).2.2
      have hpf_ne_u : π s.fst ≠ u := by
        intro h
        apply hfst_ne_piu
        have hinv := (hpi s.fst hfstW).2.1
        rw [h] at hinv
        exact hinv.symm
      have hpf_ne_piu : π s.fst ≠ π u := by
        intro h
        apply hfst_ne_u
        have hcongr := congrArg π h
        rw [(hpi s.fst hfstW).2.1, (hpi u huW).2.1] at hcongr
        exact hcongr
      have hmem : π s.fst ∈ ({s.fst, s.snd} : Finset (Fin n)) := by
        rw [hpair]
        exact Finset.mem_erase.mpr ⟨hpf_ne_piu,
          Finset.mem_erase.mpr ⟨hpf_ne_u, hpfW⟩⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact absurd h hpf_ne_fst
      · exact h
    have ht_pair : (if s.fst ∈ W ∧ s.snd ∈ W ∧ π s.fst = s.snd then (2 : ℝ) else 1) = 2 := by
      rw [ite_eq_left ⟨hfstW, hsndW, hpartner⟩]
    have ht_leg_fst : (if u ∈ W ∧ s.fst ∈ W ∧ π u = s.fst then (2 : ℝ) else 1) = 1 := by
      rw [ite_eq_right]
      rintro ⟨-, -, h⟩
      exact hfst_ne_piu h.symm
    have ht_leg_snd : (if u ∈ W ∧ s.snd ∈ W ∧ π u = s.snd then (2 : ℝ) else 1) = 1 := by
      rw [ite_eq_right]
      rintro ⟨-, -, h⟩
      exact hsnd_ne_piu h.symm
    simp only [ht_pair, ht_leg_fst, ht_leg_snd]
    norm_num



/-- `pairing`: the Pairing Lemma (paper Lemma 5.5, `lem:pairing`):
a feasible candidate family at a four-survivor level has at most
four slots; if it has four and uses every apex it is a pairing
configuration; and every pairing configuration is feasible. Proved
by the missing-vertex injection and four-cycle exclusion above.
"Feasible" here is the formal system of `IsFeasibleAt` (see its
docstring), as in the paper's "a slot imposes the relation"
reading; nothing here concludes `¬ IsRealizable` from
`¬ IsFeasibleAt`. -/
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
  refine ⟨fun H hCand hFeas => candidate_feasible_ncard_le_four S W hW H hCand hFeas,
    fun H hCand hFeas hcard hall =>
      pairingConfig_of_candidate_feasible_card_four S W hW hWS H hCand hFeas hcard hall,
    fun π H _hCand hcfg => isFeasibleAt_of_pairingConfig S W hWS π H hcfg⟩



/-- `magnitudes_forced`: the pairing system forces the six
log-magnitudes up to two parameters — cross-pair correlations of
magnitudes `a` and `b` in the block `[[a, b], [b, a]]` and within-pair
magnitudes `a * b` (paper Corollary 5.6, `cor:magnitudes`, with the
four survivors labelled `w₀ w₁ | w₂ w₃` and the relations transcribed
in the paper's index order). The paper's `W` is a set of four
survivors, so the `wᵢ` are pairwise distinct. Proved: the four
relations are a linear system in the six log-magnitudes, and
`|r| = exp (-t)` transports its solution to correlations. The
paper's converse ("every `α, β > 0` arises") is
`magnitudes_converse`. -/
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
  have hmem : ∀ x ∈ ({w₀, w₁, w₂, w₃} : Finset (Fin n)), x ∉ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  -- each relevant partial correlation has absolute value in (0, 1)
  have hpc : ∀ x ∈ ({w₀, w₁, w₂, w₃} : Finset (Fin n)),
      ∀ y ∈ ({w₀, w₁, w₂, w₃} : Finset (Fin n)), x ≠ y →
        0 < |partialCorr A S x y| ∧ |partialCorr A S x y| < 1 := by
    intro x hx y hy hxy
    have hxS := hmem x hx
    have hyS := hmem y hy
    refine ⟨?_, abs_partialCorr_lt_one hA S hxS hyS hxy⟩
    rw [abs_pos]
    unfold partialCorr
    apply div_ne_zero (hall x hx y hy hxy)
    apply Real.sqrt_ne_zero'.mpr
    exact mul_pos (schurEntry_pos hA S hxS) (schurEntry_pos hA S hyS)
  have m0 : w₀ ∈ ({w₀, w₁, w₂, w₃} : Finset (Fin n)) := by simp
  have m1 : w₁ ∈ ({w₀, w₁, w₂, w₃} : Finset (Fin n)) := by simp
  have m2 : w₂ ∈ ({w₀, w₁, w₂, w₃} : Finset (Fin n)) := by simp
  have m3 : w₃ ∈ ({w₀, w₁, w₂, w₃} : Finset (Fin n)) := by simp
  have c1 : logMag A S w₀ w₂ = logMag A S w₁ w₃ := by linarith
  have c2 : logMag A S w₀ w₃ = logMag A S w₁ w₂ := by linarith
  have c3 : logMag A S w₀ w₁ = logMag A S w₀ w₂ + logMag A S w₀ w₃ := by linarith
  -- transport logMag equalities to |partialCorr| equalities
  have key : ∀ x y : Fin n, 0 < |partialCorr A S x y| →
      |partialCorr A S x y| = Real.exp (- logMag A S x y) := by
    intro x y hpos
    rw [show -logMag A S x y = Real.log |partialCorr A S x y| from by
      simp [logMag]]
    exact (Real.exp_log hpos).symm
  refine ⟨c1, c2, c3, e1, |partialCorr A S w₀ w₂|, |partialCorr A S w₀ w₃|,
    (hpc w₀ m0 w₂ m2 h02).1, (hpc w₀ m0 w₂ m2 h02).2,
    (hpc w₀ m0 w₃ m3 h03).1, (hpc w₀ m0 w₃ m3 h03).2, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · rw [key w₁ w₃ (hpc w₁ m1 w₃ m3 h13).1, key w₀ w₂ (hpc w₀ m0 w₂ m2 h02).1, c1]
  · rw [key w₁ w₂ (hpc w₁ m1 w₂ m2 h12).1, key w₀ w₃ (hpc w₀ m0 w₃ m3 h03).1, c2]
  · rw [key w₀ w₁ (hpc w₀ m0 w₁ m1 h01).1, key w₀ w₂ (hpc w₀ m0 w₂ m2 h02).1,
      key w₀ w₃ (hpc w₀ m0 w₃ m3 h03).1, c3, neg_add, Real.exp_add]
  · rw [key w₂ w₃ (hpc w₂ m2 w₃ m3 h23).1, key w₀ w₂ (hpc w₀ m0 w₂ m2 h02).1,
      key w₀ w₃ (hpc w₀ m0 w₃ m3 h03).1, e1, neg_add, Real.exp_add]

end CholeskyCancellations

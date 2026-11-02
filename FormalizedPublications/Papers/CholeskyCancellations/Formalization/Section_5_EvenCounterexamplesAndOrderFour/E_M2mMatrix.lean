/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Section_5_EvenCounterexamplesAndOrderFour.D_PairingLemma

/-! # The `M_{2m}` family: matrix (paper Section 5)

The `M_{2m}` matrices, their pair partners, entry computations, and no-clean-ordering at the curve point. Split from `Counterexamples.lean`.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as `Defs.lean`; concrete matrices are on `Fin 4` and `Fin (2 * m)` with pair/parity read from `Finset` levels and `Fin.val` division as in the paper's `P_k = {2k, 2k+1}` indexing. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


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


variable {m : ℕ} {a b : ℝ}



/-- Partner of a vertex in its pair `P_k = {2k, 2k+1}`. -/
def m2mPartner (x : Fin (2 * m)) : Fin (2 * m) :=
  if _h : x.val % 2 = 0 then ⟨x.val + 1, by have hx := x.2; omega⟩
  else ⟨x.val - 1, by have hx := x.2; omega⟩



theorem m2mPartner_val (x : Fin (2 * m)) :
    (m2mPartner x).val = if x.val % 2 = 0 then x.val + 1 else x.val - 1 := by
  by_cases h : x.val % 2 = 0 <;> simp [m2mPartner, h]



theorem m2mPartner_ne_self (x : Fin (2 * m)) : m2mPartner x ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  rw [m2mPartner_val] at hv
  by_cases h2 : x.val % 2 = 0
  · simp [h2] at hv
  · simp [h2] at hv
    omega



theorem m2mPartner_div (x : Fin (2 * m)) :
    (m2mPartner x).val / 2 = x.val / 2 := by
  rw [m2mPartner_val]
  by_cases h : x.val % 2 = 0 <;> simp [h] <;> omega



theorem m2mPartner_mod_ne (x : Fin (2 * m)) :
    (m2mPartner x).val % 2 ≠ x.val % 2 := by
  rw [m2mPartner_val]
  by_cases h : x.val % 2 = 0 <;> simp [h] <;> omega



theorem m2mPartner_involutive : Function.Involutive (m2mPartner (m := m)) := by
  intro x
  apply Fin.ext
  have h1 := m2mPartner_val x
  have h2 := m2mPartner_val (m2mPartner x)
  have hmod := m2mPartner_mod_ne x
  by_cases h : x.val % 2 = 0
  · have hp : ¬ (m2mPartner x).val % 2 = 0 := by
      intro hp0; rw [h] at hmod; exact hmod hp0
    simp [h] at h1
    simp [hp] at h2
    omega
  · have hp : (m2mPartner x).val % 2 = 0 := by
      simp only [m2mPartner_val, h, ite_false]; omega
    simp [h] at h1
    simp [hp] at h2
    have hx1 : 1 ≤ x.val := by omega
    omega



theorem eq_m2mPartner_of_ne_of_div_eq {x y : Fin (2 * m)}
    (hxy : x ≠ y) (hdiv : x.val / 2 = y.val / 2) : y = m2mPartner x := by
  apply Fin.ext
  rw [m2mPartner_val]
  have hvy : y.val ≠ x.val := fun hh => hxy (Fin.ext hh.symm)
  by_cases h : x.val % 2 = 0 <;> simp [h] <;> omega



theorem eq_or_eq_m2mPartner_of_div_eq {x p : Fin (2 * m)}
    (hdiv : x.val / 2 = p.val / 2) : x = p ∨ x = m2mPartner p := by
  by_cases h : x = p
  · exact Or.inl h
  · exact Or.inr (eq_m2mPartner_of_ne_of_div_eq (Ne.symm h) hdiv.symm)



theorem m2m_apply_self (x : Fin (2 * m)) : m2mMatrix m a b x x = 1 := by
  simp [m2mMatrix]



theorem m2m_apply_pair {x y : Fin (2 * m)} (hxy : x ≠ y)
    (hdiv : x.val / 2 = y.val / 2) : m2mMatrix m a b x y = a * b := by
  simp [m2mMatrix, hxy, hdiv]



theorem m2m_apply_cross {x y : Fin (2 * m)}
    (hdiv : x.val / 2 ≠ y.val / 2) :
    m2mMatrix m a b x y = if x.val % 2 = y.val % 2 then a else b := by
  have hxy : x ≠ y := fun h => hdiv (by rw [h])
  simp [m2mMatrix, hxy, hdiv]



theorem m2m_entry_ne_zero (ha : 0 < a) (hb : 0 < b)
    {x y : Fin (2 * m)} (hxy : x ≠ y) : m2mMatrix m a b x y ≠ 0 := by
  by_cases hdiv : x.val / 2 = y.val / 2
  · rw [m2m_apply_pair hxy hdiv]
    exact mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)
  · rw [m2m_apply_cross hdiv]
    split
    · exact ne_of_gt ha
    · exact ne_of_gt hb



theorem m2m_pattern_adj (ha : 0 < a) (hb : 0 < b)
    {x y : Fin (2 * m)} (hxy : x ≠ y) :
    (patternGraph (m2mMatrix m a b)).Adj x y := by
  simp only [patternGraph, SimpleGraph.fromRel_adj]
  exact ⟨hxy, Or.inl (m2m_entry_ne_zero ha hb hxy)⟩



theorem m2m_predicted (ha : 0 < a) (hb : 0 < b)
    {σ : List (Fin (2 * m))} {x y : Fin (2 * m)} (hxy : x ≠ y) :
    PredictedNonzero (m2mMatrix m a b) σ x y := by
  rw [PredictedNonzero, fillGraph_adj_iff]
  have h0 : (gameGraph (patternGraph (m2mMatrix m a b))
      ([] : List (Fin (2 * m)))).Adj x y :=
    m2m_pattern_adj ha hb hxy
  have h := gameGraph_adj_mono_append (patternGraph (m2mMatrix m a b)) []
    (prefixList σ x y) x y h0
  simpa using h



theorem m2m_schurEntry_singleton
    (hM : (m2mMatrix m a b).PosDef) {p j k : Fin (2 * m)}
    (hj : j ≠ p) (hk : k ≠ p) :
    schurEntry (m2mMatrix m a b) {p} j k
      = m2mMatrix m a b j k
        - m2mMatrix m a b j p * m2mMatrix m a b k p := by
  have hj' : j ∉ insert p (∅ : Finset (Fin (2 * m))) := by simp [hj]
  have hk' : k ∉ insert p (∅ : Finset (Fin (2 * m))) := by simp [hk]
  have h := schur_quotient hM ∅ p (by simp) j k hj' hk'
  simp only [Finset.insert_empty] at h
  rw [h]
  simp [pivotEntry, schurEntry_empty, m2m_apply_self]



theorem m2m_cross_mul {p j k : Fin (2 * m)}
    (hj : j.val / 2 ≠ p.val / 2) (hk : k.val / 2 ≠ p.val / 2)
    (hpar : j.val % 2 ≠ k.val % 2) :
    m2mMatrix m a b j p * m2mMatrix m a b k p = a * b := by
  rw [m2m_apply_cross hj, m2m_apply_cross hk]
  by_cases h : j.val % 2 = p.val % 2
  · have hk2 : ¬ k.val % 2 = p.val % 2 := by omega
    simp [h, hk2]
  · have hk2 : k.val % 2 = p.val % 2 := by omega
    simp [h, hk2, mul_comm]



theorem m2m_schurEntry_singleton_partner
    (hM : (m2mMatrix m a b).PosDef) {p x : Fin (2 * m)}
    (hx : x.val / 2 ≠ p.val / 2) :
    schurEntry (m2mMatrix m a b) {p} x (m2mPartner x) = 0 := by
  have hxp : x ≠ p := fun h => hx (by rw [h])
  have hpp : m2mPartner x ≠ p := by
    intro h
    apply hx
    rw [← m2mPartner_div x, h]
  rw [m2m_schurEntry_singleton hM hxp hpp]
  have hpair : m2mMatrix m a b x (m2mPartner x) = a * b :=
    m2m_apply_pair (fun h => m2mPartner_ne_self x h.symm)
      (m2mPartner_div x).symm
  have hcross : m2mMatrix m a b x p * m2mMatrix m a b (m2mPartner x) p
      = a * b :=
    m2m_cross_mul hx (by rw [m2mPartner_div]; exact hx)
      (Ne.symm (m2mPartner_mod_ne x))
  rw [hpair, hcross]
  simp



theorem m2m_schurEntry_singleton_to_partner
    (hM : (m2mMatrix m a b).PosDef) {p x : Fin (2 * m)}
    (hx : x.val / 2 ≠ p.val / 2) :
    schurEntry (m2mMatrix m a b) {p} x (m2mPartner p)
      = if x.val % 2 = p.val % 2 then b * (1 - a ^ 2) else a * (1 - b ^ 2) := by
  have hxp : x ≠ p := fun h => hx (by rw [h])
  have hqp : m2mPartner p ≠ p := m2mPartner_ne_self p
  rw [m2m_schurEntry_singleton hM hxp hqp]
  have hMxq : m2mMatrix m a b x (m2mPartner p)
      = if x.val % 2 = (m2mPartner p).val % 2 then a else b :=
    m2m_apply_cross (by rw [m2mPartner_div]; exact hx)
  have hMxp : m2mMatrix m a b x p
      = if x.val % 2 = p.val % 2 then a else b :=
    m2m_apply_cross hx
  have hMqp : m2mMatrix m a b (m2mPartner p) p = a * b :=
    m2m_apply_pair hqp (m2mPartner_div p)
  have hmod := m2mPartner_mod_ne p
  by_cases h : x.val % 2 = p.val % 2
  · have h2 : ¬ x.val % 2 = (m2mPartner p).val % 2 :=
      fun hh => hmod (hh.symm.trans h)
    have e1 : m2mMatrix m a b x (m2mPartner p) = b := by simp [hMxq, h2]
    have e2 : m2mMatrix m a b x p = a := by simp [hMxp, h]
    rw [e1, e2, hMqp]
    simp only [h, ite_true]
    ring
  · have h2 : x.val % 2 = (m2mPartner p).val % 2 := by omega
    have e1 : m2mMatrix m a b x (m2mPartner p) = a := by simp [hMxq, h2]
    have e2 : m2mMatrix m a b x p = b := by simp [hMxp, h]
    rw [e1, e2, hMqp]
    simp only [h, ite_false]
    ring



theorem m2m_schurEntry_singleton_partner_diag
    (hM : (m2mMatrix m a b).PosDef) {p : Fin (2 * m)} :
    schurEntry (m2mMatrix m a b) {p} (m2mPartner p) (m2mPartner p)
      = 1 - (a * b) ^ 2 := by
  rw [m2m_schurEntry_singleton hM (m2mPartner_ne_self p)
      (m2mPartner_ne_self p), m2m_apply_self,
    m2m_apply_pair (m2mPartner_ne_self p) (m2mPartner_div p)]
  ring



theorem m2m_schurEntry_pair_eq_zero
    (hM : (m2mMatrix m a b).PosDef)
    (hcurve : a ^ 2 + (1 - b ^ 2) * a - 1 = 0)
    (hb : 0 < b) (hba : b < a) (ha1 : a < 1)
    {p j k : Fin (2 * m)}
    (hj : j.val / 2 ≠ p.val / 2) (hk : k.val / 2 ≠ p.val / 2)
    (hjk : j.val / 2 ≠ k.val / 2) (hpar : j.val % 2 ≠ k.val % 2) :
    schurEntry (m2mMatrix m a b) {p, m2mPartner p} j k = 0 := by
  have ha0 : 0 < a := lt_trans hb hba
  have hb1 : b < 1 := lt_trans hba ha1
  have hjp : j ≠ p := fun h => hj (by rw [h])
  have hkp : k ≠ p := fun h => hk (by rw [h])
  have hjq : j ≠ m2mPartner p := by
    intro h; apply hj; rw [h, m2mPartner_div]
  have hkq : k ≠ m2mPartner p := by
    intro h; apply hk; rw [h, m2mPartner_div]
  have hset : ({p, m2mPartner p} : Finset (Fin (2 * m)))
      = insert (m2mPartner p) {p} := by rw [Finset.pair_comm]
  have hform : schurEntry (m2mMatrix m a b)
        (insert (m2mPartner p) {p}) j k
      = schurEntry (m2mMatrix m a b) {p} j k
        - schurEntry (m2mMatrix m a b) {p} j (m2mPartner p)
          * schurEntry (m2mMatrix m a b) {p} k (m2mPartner p)
          / schurEntry (m2mMatrix m a b) {p} (m2mPartner p)
              (m2mPartner p) := by
    have hj' : j ∉ insert (m2mPartner p) ({p} : Finset (Fin (2 * m))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hjq, hjp⟩
    have hk' : k ∉ insert (m2mPartner p) ({p} : Finset (Fin (2 * m))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hkq, hkp⟩
    have h := schur_quotient hM {p} (m2mPartner p)
      (by simp [m2mPartner_ne_self p]) j k hj' hk'
    rw [h]
    rfl
  have hSjk : schurEntry (m2mMatrix m a b) {p} j k = b - a * b := by
    rw [m2m_schurEntry_singleton hM hjp hkp]
    have hMjk : m2mMatrix m a b j k = b := by
      simp [m2m_apply_cross hjk, hpar]
    rw [hMjk, m2m_cross_mul hj hk hpar]
  have hprod : schurEntry (m2mMatrix m a b) {p} j (m2mPartner p)
        * schurEntry (m2mMatrix m a b) {p} k (m2mPartner p)
      = a * b * (1 - a ^ 2) * (1 - b ^ 2) := by
    rw [m2m_schurEntry_singleton_to_partner hM hj,
      m2m_schurEntry_singleton_to_partner hM hk]
    by_cases h : j.val % 2 = p.val % 2
    · have h2 : ¬ k.val % 2 = p.val % 2 := by omega
      simp [h, h2]
      ring
    · have h2 : k.val % 2 = p.val % 2 := by omega
      simp [h, h2]
      ring
  rw [hset, hform, hSjk, hprod,
    m2m_schurEntry_singleton_partner_diag hM]
  have hab_pos : 0 < a * b := mul_pos ha0 hb
  have hab1 : a * b < 1 := by
    have h2 : a * b < a := by
      simpa using mul_lt_mul_of_pos_left hb1 ha0
    exact lt_trans h2 ha1
  have hsq : (a * b) ^ 2 < 1 := by
    nlinarith [mul_lt_mul_of_pos_left hab1 hab_pos, hab1]
  have hden : (1 : ℝ) - (a * b) ^ 2 ≠ 0 :=
    ne_of_gt (by linarith [hsq] : (0 : ℝ) < 1 - (a * b) ^ 2)
  have hkey : a * b * (1 - a ^ 2) * (1 - b ^ 2)
      = (b - a * b) * (1 - (a * b) ^ 2) := by
    linear_combination b * (1 - a) * hcurve
  rw [hkey, mul_div_cancel_right₀ _ hden]
  exact sub_self _



theorem exists_fin_ne_ne (hm : 3 ≤ m) (u v : Fin m) :
    ∃ l : Fin m, l ≠ u ∧ l ≠ v := by
  have hcard : ({u, v} : Finset (Fin m)).card ≤ 2 := by
    calc ({u, v} : Finset (Fin m)).card
        ≤ ({v} : Finset (Fin m)).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  obtain ⟨l, hl⟩ : ∃ l : Fin m, l ∉ ({u, v} : Finset (Fin m)) := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin m)) ⊆ {u, v} :=
      fun l _ => h l
    have hc := Finset.card_le_card hsub
    simp [Fintype.card_fin] at hc
    omega
  refine ⟨l, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  exact hl



theorem m2m_no_clean (hm : 3 ≤ m)
    (hcurve : a ^ 2 + (1 - b ^ 2) * a - 1 = 0)
    (hb : 0 < b) (hba : b < a) (ha1 : a < 1)
    (hM : (m2mMatrix m a b).PosDef)
    (σ : List (Fin (2 * m))) (hσ : IsOrdering σ) :
    ¬ IsCleanOrdering (m2mMatrix m a b) σ := by
  intro hclean
  have ha0 : 0 < a := lt_trans hb hba
  obtain ⟨p0, σ1, rfl⟩ : ∃ p l, σ = p :: l := by
    cases σ with
    | nil =>
        exfalso
        have hlen := hσ.2
        simp at hlen
        omega
    | cons p l => exact ⟨p, l, rfl⟩
  obtain ⟨p1, σ2, rfl⟩ : ∃ p l, σ1 = p :: l := by
    cases σ1 with
    | nil =>
        exfalso
        have hlen := hσ.2
        simp at hlen
        omega
    | cons p l => exact ⟨p, l, rfl⟩
  have hnd : p0 ∉ p1 :: σ2 := (List.nodup_cons.mp hσ.1).1
  have hnd1 : (p1 :: σ2).Nodup := (List.nodup_cons.mp hσ.1).2
  have hp0p1 : p0 ≠ p1 := by
    intro h
    apply hnd
    rw [h]
    exact List.mem_cons_self
  by_cases hq : p1 = m2mPartner p0
  · obtain ⟨p2, σ3, rfl⟩ : ∃ p l, σ2 = p :: l := by
      cases σ2 with
      | nil =>
          exfalso
          have hlen := hσ.2
          simp at hlen
          omega
      | cons p l => exact ⟨p, l, rfl⟩
    have hp0p2 : p0 ≠ p2 := by
      intro h
      apply hnd
      rw [h]
      exact List.mem_cons_of_mem _ (List.mem_cons_self)
    have hp1not : p1 ∉ p2 :: σ3 := (List.nodup_cons.mp hnd1).1
    have hp1p2 : p1 ≠ p2 := by
      intro h
      apply hp1not
      rw [h]
      exact List.mem_cons_self
    obtain ⟨l, hlu, hlv⟩ := exists_fin_ne_ne hm
      ⟨p0.val / 2, by have hlt := p0.2; omega⟩
      ⟨p2.val / 2, by have hlt := p2.2; omega⟩
    have hlu' : l.val ≠ p0.val / 2 := fun h => hlu (Fin.ext h)
    have hlv' : l.val ≠ p2.val / 2 := fun h => hlv (Fin.ext h)
    set x : Fin (2 * m) :=
      ⟨2 * l.val + (1 - p2.val % 2), by have hl := l.2; omega⟩ with hxdef
    have hxv : x.val = 2 * l.val + (1 - p2.val % 2) := rfl
    have hxdiv : x.val / 2 = l.val := by rw [hxv]; omega
    have hxmod : x.val % 2 = 1 - p2.val % 2 := by rw [hxv]; omega
    have hpar : p2.val % 2 ≠ x.val % 2 := by rw [hxmod]; omega
    have hxdiv0 : x.val / 2 ≠ p0.val / 2 := by rw [hxdiv]; exact hlu'
    have hp2xdiv : p2.val / 2 ≠ x.val / 2 := by
      rw [hxdiv]; exact fun h => hlv' h.symm
    have hp2div0 : p2.val / 2 ≠ p0.val / 2 := by
      intro hdiv
      rcases eq_or_eq_m2mPartner_of_div_eq hdiv with h | h
      · exact hp0p2 h.symm
      · exact hp1p2 (hq.trans h.symm)
    have hx0 : x ≠ p0 := fun h => hxdiv0 (by rw [h])
    have hx1 : x ≠ p1 := by
      intro h
      apply hxdiv0
      have h1 : x.val / 2 = p1.val / 2 := by rw [h]
      rw [h1, hq, m2mPartner_div]
    have hx2 : x ≠ p2 := fun h => hp2xdiv (by rw [h])
    have hzero := m2m_schurEntry_pair_eq_zero hM hcurve hb hba ha1
      hp2div0 hxdiv0 hp2xdiv hpar
    have hpref : prefixSet (p0 :: p1 :: p2 :: σ3) p2 x = {p0, p1} := by
      simp [prefixSet, prefixList, hp0p2, hp1p2, Ne.symm hx0, Ne.symm hx1]
    have hne := hclean p2 x (m2m_predicted ha0 hb (Ne.symm hx2))
    rw [hpref, hq] at hne
    exact hne hzero
  · have hx0 : m2mPartner p1 ≠ p0 := by
      intro h
      apply hq
      have h2 := congrArg m2mPartner h
      rwa [m2mPartner_involutive p1] at h2
    have hpair1 : p1.val / 2 ≠ p0.val / 2 := by
      intro hdiv
      rcases eq_or_eq_m2mPartner_of_div_eq hdiv with h | h
      · exact hp0p1 h.symm
      · exact hq h
    have hzero := m2m_schurEntry_singleton_partner hM hpair1
    have hpref : prefixSet (p0 :: p1 :: σ2) p1 (m2mPartner p1)
        = {p0} := by
      simp [prefixSet, prefixList, hp0p1, Ne.symm hx0]
    have hne := hclean p1 (m2mPartner p1)
      (m2m_predicted ha0 hb (fun h => m2mPartner_ne_self p1 h.symm))
    rw [hpref] at hne
    exact hne hzero

end CholeskyCancellations

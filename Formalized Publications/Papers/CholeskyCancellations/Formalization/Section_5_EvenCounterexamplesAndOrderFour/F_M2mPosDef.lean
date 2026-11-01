/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Section_5_EvenCounterexamplesAndOrderFour.E_M2mMatrix

/-! # The `M_{2m}` family: positive definiteness (paper Section 5)

Weights, vertex/pair/sign bookkeeping, the eigendecomposition, positive definiteness, the characteristic polynomial, the counterexample at every even order `≥ 6` (paper Theorem 5.8), and the refutation of the fill-graph conjecture (Conjecture 2.27). Split from `Counterexamples.lean`.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as `Defs.lean`; concrete matrices are on `Fin 4` and `Fin (2 * m)` with pair/parity read from `Finset` levels and `Fin.val` division as in the paper's `P_k = {2k, 2k+1}` indexing. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}
variable {m : ℕ} {a b : ℝ}


/-- The orthogonal zero-sum weights `w_k` on pair indices:
`w_k = (1, …, 1, -k, 0, …, 0)` with `k` ones. -/
def m2mW (k t : ℕ) : ℝ :=
  if t < k then 1 else if t = k then -(k : ℝ) else 0



theorem m2mW_of_lt {k t : ℕ} (h : t < k) : m2mW k t = 1 := by
  simp [m2mW, h]



theorem m2mW_self (k : ℕ) : m2mW k k = -(k : ℝ) := by
  simp [m2mW]



theorem m2mW_of_gt {k t : ℕ} (h : k < t) : m2mW k t = 0 := by
  simp [m2mW, show ¬ t < k by omega, show t ≠ k by omega]



theorem sum_range_m2mW {k : ℕ} (hk : k < m) :
    ∑ t ∈ Finset.range m, m2mW k t = 0 := by
  have h1 : ∑ t ∈ Finset.range (k + 1), m2mW k t
      = ∑ t ∈ Finset.range m, m2mW k t :=
    Finset.sum_subset (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega))
      (by
        intro t ht hts
        simp only [Finset.mem_range] at ht hts
        exact m2mW_of_gt (by omega))
  rw [← h1, Finset.sum_range_succ]
  have h2 : ∑ t ∈ Finset.range k, m2mW k t = (k : ℝ) := by
    trans ∑ _t ∈ Finset.range k, (1 : ℝ)
    · exact Finset.sum_congr rfl
        (fun t ht => m2mW_of_lt (Finset.mem_range.mp ht))
    · simp
  rw [h2, m2mW_self]
  simp



theorem m2mW_sum {k : ℕ} (hk : k < m) :
    ∑ t : Fin m, m2mW k t.val = 0 := by
  rw [Fin.sum_univ_eq_sum_range (m2mW k) m]
  exact sum_range_m2mW hk



theorem sum_range_m2mW_mul_of_lt {k l : ℕ} (hkl : k < l) (hl : l < m) :
    ∑ t ∈ Finset.range m, m2mW k t * m2mW l t = 0 := by
  have h1 : ∑ t ∈ Finset.range (k + 1), m2mW k t * m2mW l t
      = ∑ t ∈ Finset.range m, m2mW k t * m2mW l t :=
    Finset.sum_subset (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega))
      (by
        intro t ht hts
        simp only [Finset.mem_range] at ht hts
        rw [m2mW_of_gt (show k < t by omega), zero_mul])
  rw [← h1, Finset.sum_range_succ]
  have h2 : ∑ t ∈ Finset.range k, m2mW k t * m2mW l t = (k : ℝ) := by
    trans ∑ _t ∈ Finset.range k, (1 : ℝ)
    · exact Finset.sum_congr rfl (fun t ht => by
        have htk : t < k := Finset.mem_range.mp ht
        rw [m2mW_of_lt htk, m2mW_of_lt (by omega), mul_one])
    · simp
  rw [h2, m2mW_self, m2mW_of_lt hkl]
  simp



theorem m2mW_mul_sum_of_ne {k l : ℕ} (hk : k < m) (hl : l < m)
    (hkl : k ≠ l) :
    ∑ t : Fin m, m2mW k t.val * m2mW l t.val = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun t => m2mW k t * m2mW l t) m]
  rcases lt_or_gt_of_ne hkl with h | h
  · exact sum_range_m2mW_mul_of_lt h hl
  · have hsum := sum_range_m2mW_mul_of_lt h hk
    exact (Finset.sum_congr rfl
      (fun t _ => mul_comm (m2mW k t) (m2mW l t))).trans hsum



/-- Pair-major indexing equivalence `Fin m × Fin 2 ≃ Fin (2m)`. -/
def m2mVertexEquiv (m : ℕ) : Fin m × Fin 2 ≃ Fin (2 * m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))



/-- The vertex `2t + e` in pair `t` at parity `e`. -/
def m2mVertex (t : Fin m) (e : Fin 2) : Fin (2 * m) :=
  m2mVertexEquiv m (t, e)



theorem m2mVertex_val (t : Fin m) (e : Fin 2) :
    (m2mVertex t e).val = 2 * t.val + e.val := by
  have h : (m2mVertex t e).val = e.val + 2 * t.val := rfl
  omega



theorem m2mVertex_div (t : Fin m) (e : Fin 2) :
    (m2mVertex t e).val / 2 = t.val := by
  rw [m2mVertex_val]
  have he := e.2
  omega



theorem m2mVertex_mod (t : Fin m) (e : Fin 2) :
    (m2mVertex t e).val % 2 = e.val := by
  rw [m2mVertex_val]
  have he := e.2
  omega



theorem m2m_sum_split (f : Fin (2 * m) → ℝ) :
    ∑ y, f y = ∑ t : Fin m, (f (m2mVertex t 0) + f (m2mVertex t 1)) := by
  calc ∑ y, f y = ∑ p : Fin m × Fin 2, f (m2mVertexEquiv m p) :=
        (Equiv.sum_comp _ _).symm
    _ = ∑ t, ∑ e, f (m2mVertex t e) := Fintype.sum_prod_type _
    _ = ∑ t, (f (m2mVertex t 0) + f (m2mVertex t 1)) :=
        Finset.sum_congr rfl (fun t _ => Fin.sum_univ_two _)



/-- The pair index of a vertex, as an element of `Fin m`. -/
def m2mPair (x : Fin (2 * m)) : Fin m :=
  ⟨x.val / 2, by have hx := x.2; omega⟩



theorem m2mPair_val (x : Fin (2 * m)) : (m2mPair x).val = x.val / 2 := rfl



theorem m2mPair_vertex (t : Fin m) (e : Fin 2) :
    m2mPair (m2mVertex t e) = t :=
  Fin.ext (by rw [m2mPair_val, m2mVertex_div])



/-- Parity sign of a vertex. -/
def m2mSign (x : Fin (2 * m)) : ℝ := if x.val % 2 = 0 then 1 else -1



theorem m2mSign_vertex_zero (t : Fin m) :
    m2mSign (m2mVertex t 0) = 1 := by
  simp [m2mSign, m2mVertex_mod]



theorem m2mSign_vertex_one (t : Fin m) :
    m2mSign (m2mVertex t 1) = -1 := by
  simp [m2mSign, m2mVertex_mod]



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



theorem m2mP_vertex_zero (t : Fin m) (c : Fin (2 * m)) :
    m2mP m (m2mVertex t 0) c = m2mU c t + m2mV c t := by
  simp [m2mP, m2mPair_vertex, m2mSign_vertex_zero]



theorem m2mP_vertex_one (t : Fin m) (c : Fin (2 * m)) :
    m2mP m (m2mVertex t 1) c = m2mU c t - m2mV c t := by
  simp [m2mP, m2mPair_vertex, m2mSign_vertex_one, sub_eq_add_neg]



/-- The eigenvalue of column `c` of `m2mP m`. -/
def m2mEigen (m : ℕ) (a b : ℝ) (c : Fin (2 * m)) : ℝ :=
  if c.val = 0 then 1 + a * b + (a + b) * ((m : ℝ) - 1)
  else if c.val = 1 then 1 - a * b + (a - b) * ((m : ℝ) - 1)
  else if c.val % 2 = 0 then (1 - a) * (1 - b)
  else (1 - a) * (1 + b)



theorem m2mMatrix_vertex (x : Fin (2 * m)) (t : Fin m) (e : Fin 2) :
    m2mMatrix m a b x (m2mVertex t e)
      = if t = m2mPair x then (if x.val % 2 = e.val then 1 else a * b)
        else (if x.val % 2 = e.val then a else b) := by
  by_cases ht : t = m2mPair x
  · by_cases he : x.val % 2 = e.val
    · have hxy : m2mVertex t e = x := by
        apply Fin.ext
        rw [m2mVertex_val]
        have htval : t.val = x.val / 2 := by rw [ht]; rfl
        omega
      rw [hxy, m2m_apply_self]
      simp [ht, he]
    · have hne : x ≠ m2mVertex t e := by
        intro h
        apply he
        rw [← m2mVertex_mod t e, h]
      have hdiv : x.val / 2 = (m2mVertex t e).val / 2 := by
        rw [m2mVertex_div, ht]; rfl
      rw [m2m_apply_pair hne hdiv]
      simp [ht, he]
  · have hdiv : x.val / 2 ≠ (m2mVertex t e).val / 2 := by
      rw [m2mVertex_div]
      intro h
      apply ht
      apply Fin.ext
      rw [m2mPair_val]
      exact h.symm
    rw [m2m_apply_cross hdiv]
    by_cases he : x.val % 2 = e.val <;> simp [ht, he, m2mVertex_mod]



theorem m2mU_sum (c : Fin (2 * m)) :
    ∑ t : Fin m, m2mU c t = if c.val = 0 then (m : ℝ) else 0 := by
  by_cases h0 : c.val = 0
  · simp [m2mU, h0]
  by_cases h1 : c.val = 1
  · simp [m2mU, h1]
  by_cases hev : c.val % 2 = 0
  · have hk : c.val / 2 < m := by have hc := c.2; omega
    have hpt : ∀ t : Fin m, m2mU c t = m2mW (c.val / 2) t.val :=
      fun t => by simp [m2mU, h0, h1, hev]
    refine Eq.trans (Finset.sum_congr rfl fun t _ => hpt t) ?_
    rw [m2mW_sum hk]
    simp [h0]
  · have hpt : ∀ t : Fin m, m2mU c t = 0 :=
      fun t => by simp [m2mU, h0, h1, hev]
    simp [hpt, h0]



theorem m2mV_sum (c : Fin (2 * m)) :
    ∑ t : Fin m, m2mV c t = if c.val = 1 then (m : ℝ) else 0 := by
  by_cases h0 : c.val = 0
  · simp [m2mV, h0]
  by_cases h1 : c.val = 1
  · simp [m2mV, h1]
  by_cases hev : c.val % 2 = 0
  · have hpt : ∀ t : Fin m, m2mV c t = 0 :=
      fun t => by simp [m2mV, h0, h1, hev]
    simp [hpt, h1]
  · have hk : c.val / 2 < m := by have hc := c.2; omega
    have hpt : ∀ t : Fin m, m2mV c t = m2mW (c.val / 2) t.val :=
      fun t => by simp [m2mV, h0, h1, hev]
    refine Eq.trans (Finset.sum_congr rfl fun t _ => hpt t) ?_
    rw [m2mW_sum hk]
    simp [h1]



theorem m2mU_cases (c : Fin (2 * m)) :
    (∀ t, m2mU c t = 0)
      ∨ (c.val = 0 ∧ ∀ t, m2mU c t = 1)
      ∨ (∃ k, c.val = 2 * k ∧ k < m
          ∧ ∀ t, m2mU c t = m2mW k t.val) := by
  by_cases h0 : c.val = 0
  · exact Or.inr (Or.inl ⟨h0, fun t => by simp [m2mU, h0]⟩)
  by_cases h1 : c.val = 1
  · exact Or.inl (fun t => by simp [m2mU, h1])
  by_cases hev : c.val % 2 = 0
  · exact Or.inr (Or.inr ⟨c.val / 2, by omega,
      by have hc := c.2; omega,
      fun t => by simp [m2mU, h0, h1, hev]⟩)
  · exact Or.inl (fun t => by simp [m2mU, h0, h1, hev])



theorem m2mV_cases (c : Fin (2 * m)) :
    (∀ t, m2mV c t = 0)
      ∨ (c.val = 1 ∧ ∀ t, m2mV c t = 1)
      ∨ (∃ k, c.val = 2 * k + 1 ∧ k < m
          ∧ ∀ t, m2mV c t = m2mW k t.val) := by
  by_cases h0 : c.val = 0
  · exact Or.inl (fun t => by simp [m2mV, h0])
  by_cases h1 : c.val = 1
  · exact Or.inr (Or.inl ⟨h1, fun t => by simp [m2mV, h1]⟩)
  by_cases hev : c.val % 2 = 0
  · exact Or.inl (fun t => by simp [m2mV, h0, h1, hev])
  · exact Or.inr (Or.inr ⟨c.val / 2, by omega,
      by have hc := c.2; omega,
      fun t => by simp [m2mV, h0, h1, hev]⟩)



theorem m2mU_mul_sum_eq_zero {c d : Fin (2 * m)} (hcd : c ≠ d) :
    ∑ t : Fin m, m2mU c t * m2mU d t = 0 := by
  rcases m2mU_cases c with hc | hc | hc <;>
    rcases m2mU_cases d with hd | hd | hd
  · simp [hc]
  · simp [hc]
  · simp [hc]
  · simp [hd]
  · exact absurd (Fin.ext (hc.1.trans hd.1.symm)) hcd
  · obtain ⟨k, _hkv, hkm, hk⟩ := hd
    calc ∑ t : Fin m, m2mU c t * m2mU d t
        = ∑ t : Fin m, m2mW k t.val :=
          Finset.sum_congr rfl (fun t _ => by simp [hc.2 t, hk t])
      _ = 0 := m2mW_sum hkm
  · simp [hd]
  · obtain ⟨k, _hkv, hkm, hk⟩ := hc
    calc ∑ t : Fin m, m2mU c t * m2mU d t
        = ∑ t : Fin m, m2mW k t.val :=
          Finset.sum_congr rfl (fun t _ => by simp [hk t, hd.2 t])
      _ = 0 := m2mW_sum hkm
  · obtain ⟨k, hkv, hkm, hk⟩ := hc
    obtain ⟨l, hlv, hlm, hl⟩ := hd
    by_cases hkl : k = l
    · subst hkl
      exact absurd (Fin.ext (hkv.trans hlv.symm)) hcd
    · calc ∑ t : Fin m, m2mU c t * m2mU d t
          = ∑ t : Fin m, m2mW k t.val * m2mW l t.val :=
            Finset.sum_congr rfl (fun t _ => by simp [hk t, hl t])
        _ = 0 := m2mW_mul_sum_of_ne hkm hlm hkl



theorem m2mV_mul_sum_eq_zero {c d : Fin (2 * m)} (hcd : c ≠ d) :
    ∑ t : Fin m, m2mV c t * m2mV d t = 0 := by
  rcases m2mV_cases c with hc | hc | hc <;>
    rcases m2mV_cases d with hd | hd | hd
  · simp [hc]
  · simp [hc]
  · simp [hc]
  · simp [hd]
  · exact absurd (Fin.ext (hc.1.trans hd.1.symm)) hcd
  · obtain ⟨k, _hkv, hkm, hk⟩ := hd
    calc ∑ t : Fin m, m2mV c t * m2mV d t
        = ∑ t : Fin m, m2mW k t.val :=
          Finset.sum_congr rfl (fun t _ => by simp [hc.2 t, hk t])
      _ = 0 := m2mW_sum hkm
  · simp [hd]
  · obtain ⟨k, _hkv, hkm, hk⟩ := hc
    calc ∑ t : Fin m, m2mV c t * m2mV d t
        = ∑ t : Fin m, m2mW k t.val :=
          Finset.sum_congr rfl (fun t _ => by simp [hk t, hd.2 t])
      _ = 0 := m2mW_sum hkm
  · obtain ⟨k, hkv, hkm, hk⟩ := hc
    obtain ⟨l, hlv, hlm, hl⟩ := hd
    by_cases hkl : k = l
    · subst hkl
      exact absurd (Fin.ext (hkv.trans hlv.symm)) hcd
    · calc ∑ t : Fin m, m2mV c t * m2mV d t
          = ∑ t : Fin m, m2mW k t.val * m2mW l t.val :=
            Finset.sum_congr rfl (fun t _ => by simp [hk t, hl t])
        _ = 0 := m2mW_mul_sum_of_ne hkm hlm hkl



/-- Squared norm of column `c` of `m2mP m`. -/
def m2mNorm (c : Fin (2 * m)) : ℝ :=
  ∑ x, m2mP m x c * m2mP m x c



theorem m2mP_zero {c : Fin (2 * m)} (hm : 0 < 2 * m) :
    m2mP m ⟨0, hm⟩ c = 1 := by
  have hm0 : 0 < m := by omega
  by_cases h0 : c.val = 0
  · simp [m2mP, m2mSign, m2mU, m2mV, h0]
  by_cases h1 : c.val = 1
  · simp [m2mP, m2mSign, m2mU, m2mV, h1]
  by_cases hev : c.val % 2 = 0
  · have hk : m2mW (c.val / 2) 0 = 1 :=
      m2mW_of_lt (by omega)
    simp [m2mP, m2mPair, m2mSign, m2mU, m2mV, h0, h1, hev, hk]
  · have hk : m2mW (c.val / 2) 0 = 1 :=
      m2mW_of_lt (by omega)
    simp [m2mP, m2mPair, m2mSign, m2mU, m2mV, h0, h1, hev, hk]



theorem m2mNorm_pos (c : Fin (2 * m)) : 0 < m2mNorm c := by
  have hm : 0 < 2 * m := by have hc := c.2; omega
  have h1 : (1 : ℝ) ≤ m2mNorm c := by
    calc (1 : ℝ) = m2mP m ⟨0, hm⟩ c * m2mP m ⟨0, hm⟩ c := by
          rw [m2mP_zero hm]; norm_num
      _ ≤ ∑ x, m2mP m x c * m2mP m x c :=
          Finset.single_le_sum
            (f := fun x => m2mP m x c * m2mP m x c)
            (fun i _ => mul_self_nonneg _) (Finset.mem_univ _)
      _ = m2mNorm c := rfl
  linarith



theorem m2mP_transpose_mul_self :
    (m2mP m).transpose * m2mP m = Matrix.diagonal m2mNorm := by
  ext c d
  by_cases hcd : c = d
  · subst hcd
    simp [Matrix.mul_apply, m2mNorm]
  · have hsum : ∑ x, m2mP m x c * m2mP m x d = 0 := by
      rw [m2m_sum_split]
      have hpair : ∀ t : Fin m,
          m2mP m (m2mVertex t 0) c * m2mP m (m2mVertex t 0) d
            + m2mP m (m2mVertex t 1) c * m2mP m (m2mVertex t 1) d
          = 2 * (m2mU c t * m2mU d t + m2mV c t * m2mV d t) := by
        intro t
        rw [m2mP_vertex_zero, m2mP_vertex_one,
          m2mP_vertex_zero, m2mP_vertex_one]
        ring
      calc ∑ t : Fin m, (m2mP m (m2mVertex t 0) c
              * m2mP m (m2mVertex t 0) d
            + m2mP m (m2mVertex t 1) c * m2mP m (m2mVertex t 1) d)
          = ∑ t : Fin m, 2 * (m2mU c t * m2mU d t
              + m2mV c t * m2mV d t) :=
            Finset.sum_congr rfl (fun t _ => hpair t)
        _ = 2 * ∑ t : Fin m, (m2mU c t * m2mU d t
              + m2mV c t * m2mV d t) := by rw [Finset.mul_sum]
        _ = 0 := by
            rw [Finset.sum_add_distrib, m2mU_mul_sum_eq_zero hcd,
              m2mV_mul_sum_eq_zero hcd]
            simp
    simp [Matrix.mul_apply, hcd, hsum]



theorem m2mP_isUnit : IsUnit (m2mP m) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet : (m2mP m).det ≠ 0 := by
    intro hzero
    have h1 : ((m2mP m).transpose * m2mP m).det = ∏ c : Fin (2 * m), m2mNorm c := by
      rw [m2mP_transpose_mul_self, Matrix.det_diagonal]
    rw [Matrix.det_mul, Matrix.det_transpose, hzero, mul_zero] at h1
    have hpos : 0 < ∏ c : Fin (2 * m), m2mNorm c :=
      Finset.prod_pos (fun c _ => m2mNorm_pos c)
    exact ne_of_gt hpos h1.symm
  exact isUnit_iff_ne_zero.mpr hdet



theorem m2mP_inv :
    (m2mP m)⁻¹
      = Matrix.diagonal (fun c => (m2mNorm c)⁻¹) * (m2mP m).transpose := by
  apply Matrix.inv_eq_left_inv
  calc Matrix.diagonal (fun c => (m2mNorm c)⁻¹) * (m2mP m).transpose * m2mP m
      = Matrix.diagonal (fun c => (m2mNorm c)⁻¹)
          * ((m2mP m).transpose * m2mP m) := Matrix.mul_assoc _ _ _
    _ = Matrix.diagonal (fun c => (m2mNorm c)⁻¹)
          * Matrix.diagonal m2mNorm := by
        rw [m2mP_transpose_mul_self]
    _ = 1 := by
        rw [Matrix.diagonal_mul_diagonal]
        have hfun : (fun c : Fin (2 * m) => (m2mNorm c)⁻¹ * m2mNorm c)
            = fun _ => (1 : ℝ) := by
          funext c
          exact inv_mul_cancel₀ (ne_of_gt (m2mNorm_pos c))
        rw [hfun]
        exact Matrix.diagonal_one



theorem m2m_mul_P :
    m2mMatrix m a b * m2mP m
      = m2mP m * Matrix.diagonal (m2mEigen m a b) := by
  ext x c
  rw [Matrix.mul_diagonal, Matrix.mul_apply,
    m2m_sum_split (fun y => m2mMatrix m a b x y * m2mP m y c)]
  have hcontrib : ∀ t : Fin m,
      m2mMatrix m a b x (m2mVertex t 0) * m2mP m (m2mVertex t 0) c
        + m2mMatrix m a b x (m2mVertex t 1) * m2mP m (m2mVertex t 1) c
      = if t = m2mPair x then
          (1 + a * b) * m2mU c t + m2mSign x * ((1 - a * b) * m2mV c t)
        else
          (a + b) * m2mU c t + m2mSign x * ((a - b) * m2mV c t) := by
    intro t
    rw [m2mMatrix_vertex, m2mMatrix_vertex,
      m2mP_vertex_zero, m2mP_vertex_one]
    by_cases ht : t = m2mPair x <;> by_cases hx : x.val % 2 = 0
    · simp [ht, hx, m2mSign]
      ring
    · have hx1 : x.val % 2 = 1 := by omega
      simp [ht, hx1, m2mSign]
      ring
    · simp [ht, hx, m2mSign]
      ring
    · have hx1 : x.val % 2 = 1 := by omega
      simp [ht, hx1, m2mSign]
      ring
  refine Eq.trans (Finset.sum_congr rfl fun t _ => hcontrib t) ?_
  have hUcompl : ∑ t ∈ Finset.univ \ {m2mPair x}, m2mU c t
      = (∑ t, m2mU c t) - m2mU c (m2mPair x) := by
    have h := Finset.sum_eq_add_sum_sdiff_singleton_of_mem
      (Finset.mem_univ (m2mPair x)) (m2mU c)
    linarith [h]
  have hVcompl : ∑ t ∈ Finset.univ \ {m2mPair x}, m2mV c t
      = (∑ t, m2mV c t) - m2mV c (m2mPair x) := by
    have h := Finset.sum_eq_add_sum_sdiff_singleton_of_mem
      (Finset.mem_univ (m2mPair x)) (m2mV c)
    linarith [h]
  have hB : ∑ t ∈ Finset.univ \ {m2mPair x},
        (if t = m2mPair x then
          (1 + a * b) * m2mU c t + m2mSign x * ((1 - a * b) * m2mV c t)
        else
          (a + b) * m2mU c t + m2mSign x * ((a - b) * m2mV c t))
      = (a + b) * ((∑ t, m2mU c t) - m2mU c (m2mPair x))
        + m2mSign x * ((a - b) * ((∑ t, m2mV c t)
            - m2mV c (m2mPair x))) := by
    calc ∑ t ∈ Finset.univ \ {m2mPair x},
          (if t = m2mPair x then
            (1 + a * b) * m2mU c t + m2mSign x * ((1 - a * b) * m2mV c t)
          else
            (a + b) * m2mU c t + m2mSign x * ((a - b) * m2mV c t))
        = ∑ t ∈ Finset.univ \ {m2mPair x},
            ((a + b) * m2mU c t
              + m2mSign x * ((a - b) * m2mV c t)) :=
          Finset.sum_congr rfl (fun t ht => by
            have htne : t ≠ m2mPair x := by
              simpa using (Finset.mem_sdiff.mp ht).2
            simp only [htne, ite_false])
      _ = (a + b) * (∑ t ∈ Finset.univ \ {m2mPair x}, m2mU c t)
            + m2mSign x * ((a - b)
              * (∑ t ∈ Finset.univ \ {m2mPair x}, m2mV c t)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (a + b) * ((∑ t, m2mU c t) - m2mU c (m2mPair x))
            + m2mSign x * ((a - b) * ((∑ t, m2mV c t)
                - m2mV c (m2mPair x))) := by
          rw [hUcompl, hVcompl]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem
    (Finset.mem_univ (m2mPair x)) _]
  simp only [ite_true]
  rw [hB]
  by_cases h0 : c.val = 0
  · have hSU : (∑ t, m2mU c t) = (m : ℝ) := by
      rw [m2mU_sum]; simp [h0]
    have hSV : (∑ t, m2mV c t) = 0 := by
      rw [m2mV_sum]; simp [show c.val ≠ 1 by omega]
    have hU : m2mU c (m2mPair x) = 1 := by simp [m2mU, h0]
    have hV : m2mV c (m2mPair x) = 0 := by simp [m2mV, h0]
    have hE : m2mEigen m a b c
        = 1 + a * b + (a + b) * ((m : ℝ) - 1) := by
      simp [m2mEigen, h0]
    rw [hSU, hSV, hU, hV, hE]
    simp only [m2mP]
    rw [hU, hV]
    ring
  by_cases h1 : c.val = 1
  · have hSU : (∑ t, m2mU c t) = 0 := by
      rw [m2mU_sum]; simp [h0]
    have hSV : (∑ t, m2mV c t) = (m : ℝ) := by
      rw [m2mV_sum]; simp [h1]
    have hU : m2mU c (m2mPair x) = 0 := by simp [m2mU, h1]
    have hV : m2mV c (m2mPair x) = 1 := by simp [m2mV, h1]
    have hE : m2mEigen m a b c
        = 1 - a * b + (a - b) * ((m : ℝ) - 1) := by
      simp [m2mEigen, h1]
    rw [hSU, hSV, hU, hV, hE]
    simp only [m2mP]
    rw [hU, hV]
    ring
  by_cases hev : c.val % 2 = 0
  · have hSU : (∑ t, m2mU c t) = 0 := by
      rw [m2mU_sum]; simp [h0]
    have hSV : (∑ t, m2mV c t) = 0 := by
      rw [m2mV_sum]; simp [h1]
    have hV : m2mV c (m2mPair x) = 0 := by simp [m2mV, h0, h1, hev]
    have hE : m2mEigen m a b c = (1 - a) * (1 - b) := by
      simp [m2mEigen, h0, h1, hev]
    rw [hSU, hSV, hV, hE]
    simp only [m2mP]
    rw [hV]
    ring
  · have hSU : (∑ t, m2mU c t) = 0 := by
      rw [m2mU_sum]; simp [h0]
    have hSV : (∑ t, m2mV c t) = 0 := by
      rw [m2mV_sum]; simp [h1]
    have hU : m2mU c (m2mPair x) = 0 := by simp [m2mU, h0, h1, hev]
    have hE : m2mEigen m a b c = (1 - a) * (1 + b) := by
      simp [m2mEigen, h0, h1, hev]
    rw [hSU, hSV, hU, hE]
    simp only [m2mP]
    rw [hU]
    ring



theorem m2mEigen_pos (hm : 2 ≤ m) (hb : 0 < b) (hba : b < a)
    (ha1 : a < 1) (c : Fin (2 * m)) : 0 < m2mEigen m a b c := by
  have ha0 : 0 < a := lt_trans hb hba
  have hb1 : b < 1 := lt_trans hba ha1
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hab1 : a * b < 1 := by
    have h2 : a * b < a := by
      simpa using mul_lt_mul_of_pos_left hb1 ha0
    exact lt_trans h2 ha1
  by_cases h0 : c.val = 0
  · have hE : m2mEigen m a b c
        = 1 + a * b + (a + b) * ((m : ℝ) - 1) := by
      simp [m2mEigen, h0]
    rw [hE]
    nlinarith [mul_pos ha0 hb,
      mul_nonneg (show (0 : ℝ) ≤ a + b by linarith)
        (show (0 : ℝ) ≤ (m : ℝ) - 1 by linarith)]
  by_cases h1 : c.val = 1
  · have hE : m2mEigen m a b c
        = 1 - a * b + (a - b) * ((m : ℝ) - 1) := by
      simp [m2mEigen, h1]
    rw [hE]
    nlinarith [hab1,
      mul_nonneg (show (0 : ℝ) ≤ a - b by linarith)
        (show (0 : ℝ) ≤ (m : ℝ) - 1 by linarith)]
  by_cases hev : c.val % 2 = 0
  · have hE : m2mEigen m a b c = (1 - a) * (1 - b) := by
      simp [m2mEigen, h0, h1, hev]
    rw [hE]
    exact mul_pos (by linarith) (by linarith)
  · have hE : m2mEigen m a b c = (1 - a) * (1 + b) := by
      simp [m2mEigen, h0, h1, hev]
    rw [hE]
    exact mul_pos (by linarith) (by linarith)



theorem m2m_posDef (hm : 2 ≤ m) (hb : 0 < b) (hba : b < a)
    (ha1 : a < 1) : (m2mMatrix m a b).PosDef := by
  have hdet : IsUnit (m2mP m).det :=
    (Matrix.isUnit_iff_isUnit_det (m2mP m)).mp m2mP_isUnit
  have hMeq : m2mMatrix m a b
      = m2mP m * Matrix.diagonal (m2mEigen m a b) * (m2mP m)⁻¹ := by
    calc m2mMatrix m a b
        = m2mMatrix m a b * m2mP m * (m2mP m)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
            Matrix.mul_one]
      _ = m2mP m * Matrix.diagonal (m2mEigen m a b) * (m2mP m)⁻¹ := by
          rw [m2m_mul_P]
  have hfact : m2mMatrix m a b
      = m2mP m
        * Matrix.diagonal (fun c => m2mEigen m a b c / m2mNorm c)
        * (m2mP m).conjTranspose := by
    have hconj : (m2mP m).conjTranspose = (m2mP m).transpose := by
      ext i j
      simp [Matrix.conjTranspose]
    have hdiag : Matrix.diagonal (m2mEigen m a b)
          * Matrix.diagonal (fun c => (m2mNorm c)⁻¹)
        = Matrix.diagonal (fun c => m2mEigen m a b c / m2mNorm c) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
    rw [hMeq, m2mP_inv, ← hconj, ← hdiag]
    simp only [Matrix.mul_assoc]
  have hD : (Matrix.diagonal
      (fun c => m2mEigen m a b c / m2mNorm c)).PosDef :=
    Matrix.PosDef.diagonal (fun c =>
      div_pos (m2mEigen_pos hm hb hba ha1 c) (m2mNorm_pos c))
  have hcong := hD.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit m2mP_isUnit)
  rwa [hfact]



/-- Eigenvalues of `M₄` are positive for all `a, b ∈ (0, 1)`, with
no order between them: the `c = 1` eigenvalue is `(1 + a)(1 - b)`
when `m = 2`. -/
theorem m2mEigen_pos_two (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b)
    (hb1 : b < 1) (c : Fin (2 * 2)) : 0 < m2mEigen 2 a b c := by
  by_cases h0 : c.val = 0
  · have hE : m2mEigen 2 a b c = 1 + a * b + (a + b) := by
      simp [m2mEigen, h0]
      ring
    rw [hE]
    nlinarith [mul_pos ha hb]
  by_cases h1 : c.val = 1
  · have hE : m2mEigen 2 a b c = (1 + a) * (1 - b) := by
      simp [m2mEigen, h1]
      ring
    rw [hE]
    exact mul_pos (by linarith) (by linarith)
  by_cases hev : c.val % 2 = 0
  · have hE : m2mEigen 2 a b c = (1 - a) * (1 - b) := by
      simp [m2mEigen, h0, h1, hev]
    rw [hE]
    exact mul_pos (by linarith) (by linarith)
  · have hE : m2mEigen 2 a b c = (1 - a) * (1 + b) := by
      simp [m2mEigen, h0, h1, hev]
    rw [hE]
    exact mul_pos (by linarith) (by linarith)



/-- `M₄` is positive definite for all `a, b ∈ (0, 1)`. Same
congruence argument as `m2m_posDef`, with `m2mEigen_pos_two`. -/
theorem m2m_posDef_two (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b)
    (hb1 : b < 1) : (m2mMatrix 2 a b).PosDef := by
  have hdet : IsUnit (m2mP 2).det :=
    (Matrix.isUnit_iff_isUnit_det (m2mP 2)).mp m2mP_isUnit
  have hMeq : m2mMatrix 2 a b
      = m2mP 2 * Matrix.diagonal (m2mEigen 2 a b) * (m2mP 2)⁻¹ := by
    calc m2mMatrix 2 a b
        = m2mMatrix 2 a b * m2mP 2 * (m2mP 2)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
            Matrix.mul_one]
      _ = m2mP 2 * Matrix.diagonal (m2mEigen 2 a b) * (m2mP 2)⁻¹ := by
          rw [m2m_mul_P]
  have hfact : m2mMatrix 2 a b
      = m2mP 2
        * Matrix.diagonal (fun c => m2mEigen 2 a b c / m2mNorm c)
        * (m2mP 2).conjTranspose := by
    have hconj : (m2mP 2).conjTranspose = (m2mP 2).transpose := by
      ext i j
      simp [Matrix.conjTranspose]
    have hdiag : Matrix.diagonal (m2mEigen 2 a b)
          * Matrix.diagonal (fun c => (m2mNorm c)⁻¹)
        = Matrix.diagonal (fun c => m2mEigen 2 a b c / m2mNorm c) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
    rw [hMeq, m2mP_inv, ← hconj, ← hdiag]
    simp only [Matrix.mul_assoc]
  have hD : (Matrix.diagonal
      (fun c => m2mEigen 2 a b c / m2mNorm c)).PosDef :=
    Matrix.PosDef.diagonal (fun c =>
      div_pos (m2mEigen_pos_two ha ha1 hb hb1 c) (m2mNorm_pos c))
  have hcong := hD.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit m2mP_isUnit)
  rwa [hfact]



/-- The converse in paper Corollary 5.6 (`cor:magnitudes`): every
pair `α, β > 0` arises. Realized at level `∅` by
`M₄ = m2mMatrix 2 (exp (-α)) (exp (-β))` on the survivors
`0 1 | 2 3`, with diagonal entries `1`. -/
theorem magnitudes_converse (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ A : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℝ, A.PosDef ∧
      logMag A ∅ 0 2 = α ∧ logMag A ∅ 1 3 = α ∧
      logMag A ∅ 0 3 = β ∧ logMag A ∅ 1 2 = β ∧
      logMag A ∅ 0 1 = α + β ∧ logMag A ∅ 2 3 = α + β := by
  have heα : (0 : ℝ) < Real.exp (-α) := Real.exp_pos _
  have heβ : (0 : ℝ) < Real.exp (-β) := Real.exp_pos _
  have heα1 : Real.exp (-α) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have heβ1 : Real.exp (-β) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  refine ⟨m2mMatrix 2 (Real.exp (-α)) (Real.exp (-β)),
    m2m_posDef_two heα heα1 heβ heβ1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h02 : m2mMatrix 2 (Real.exp (-α)) (Real.exp (-β))
        (0 : Fin (2 * 2)) 2 = Real.exp (-α) := by
      rw [m2m_apply_cross (by decide)]
      simp
    simp [logMag, partialCorr, schurEntry_empty, h02,
      m2m_apply_self, abs_of_pos heα]
  · have h13 : m2mMatrix 2 (Real.exp (-α)) (Real.exp (-β))
        (1 : Fin (2 * 2)) 3 = Real.exp (-α) := by
      rw [m2m_apply_cross (by decide)]
      simp
    simp [logMag, partialCorr, schurEntry_empty, h13,
      m2m_apply_self, abs_of_pos heα]
  · have h03 : m2mMatrix 2 (Real.exp (-α)) (Real.exp (-β))
        (0 : Fin (2 * 2)) 3 = Real.exp (-β) := by
      rw [m2m_apply_cross (by decide)]
      simp
    simp [logMag, partialCorr, schurEntry_empty, h03,
      m2m_apply_self, abs_of_pos heβ]
  · have h12 : m2mMatrix 2 (Real.exp (-α)) (Real.exp (-β))
        (1 : Fin (2 * 2)) 2 = Real.exp (-β) := by
      rw [m2m_apply_cross (by decide)]
      simp
    simp [logMag, partialCorr, schurEntry_empty, h12,
      m2m_apply_self, abs_of_pos heβ]
  · have h01 : m2mMatrix 2 (Real.exp (-α)) (Real.exp (-β))
        (0 : Fin (2 * 2)) 1 = Real.exp (-α) * Real.exp (-β) := by
      rw [m2m_apply_pair (by decide) (by decide)]
    simp [logMag, partialCorr, schurEntry_empty, h01,
      m2m_apply_self, abs_of_pos (mul_pos heα heβ),
      Real.log_mul (ne_of_gt heα) (ne_of_gt heβ)]
    ring
  · have h23 : m2mMatrix 2 (Real.exp (-α)) (Real.exp (-β))
        (2 : Fin (2 * 2)) 3 = Real.exp (-α) * Real.exp (-β) := by
      rw [m2m_apply_pair (by decide) (by decide)]
    simp [logMag, partialCorr, schurEntry_empty, h23,
      m2m_apply_self, abs_of_pos (mul_pos heα heβ),
      Real.log_mul (ne_of_gt heα) (ne_of_gt heβ)]
    ring




theorem m2m_charpoly (hm : 2 ≤ m) :
    (m2mMatrix m a b).charpoly
      = (Polynomial.X
          - Polynomial.C (1 + a * b + (a + b) * ((m : ℝ) - 1)))
        * (Polynomial.X
          - Polynomial.C (1 - a * b + (a - b) * ((m : ℝ) - 1)))
        * (Polynomial.X - Polynomial.C ((1 - a) * (1 - b))) ^ (m - 1)
        * (Polynomial.X - Polynomial.C ((1 - a) * (1 + b)))
          ^ (m - 1) := by
  have hdet : IsUnit (m2mP m).det :=
    (Matrix.isUnit_iff_isUnit_det (m2mP m)).mp m2mP_isUnit
  have hMeq : m2mMatrix m a b
      = m2mP m * Matrix.diagonal (m2mEigen m a b) * (m2mP m)⁻¹ := by
    calc m2mMatrix m a b
        = m2mMatrix m a b * m2mP m * (m2mP m)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
            Matrix.mul_one]
      _ = m2mP m * Matrix.diagonal (m2mEigen m a b) * (m2mP m)⁻¹ := by
          rw [m2m_mul_P]
  set U : (Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)ˣ :=
    Matrix.nonsingInvUnit (m2mP m) hdet with hUdef
  have hchar : (m2mMatrix m a b).charpoly
      = (Matrix.diagonal (m2mEigen m a b)).charpoly := by
    have h := Matrix.charpoly_units_conj U
      (Matrix.diagonal (m2mEigen m a b))
    rw [hMeq]
    exact h
  rw [hchar, Matrix.charpoly_diagonal]
  have hinner : ∀ t : Fin m,
      ∏ e : Fin 2, (Polynomial.X
          - Polynomial.C (m2mEigen m a b (m2mVertex t e)))
        = if t = (⟨0, by omega⟩ : Fin m) then
            (Polynomial.X
              - Polynomial.C (1 + a * b + (a + b) * ((m : ℝ) - 1)))
            * (Polynomial.X
              - Polynomial.C (1 - a * b + (a - b) * ((m : ℝ) - 1)))
          else
            (Polynomial.X - Polynomial.C ((1 - a) * (1 - b)))
            * (Polynomial.X - Polynomial.C ((1 - a) * (1 + b))) := by
    intro t
    rw [Fin.prod_univ_two]
    have e0 : m2mEigen m a b (m2mVertex t 0)
        = if t = (⟨0, by omega⟩ : Fin m)
          then 1 + a * b + (a + b) * ((m : ℝ) - 1)
          else (1 - a) * (1 - b) := by
      by_cases ht : t.val = 0
      · have ht0 : t = (⟨0, by omega⟩ : Fin m) := Fin.ext ht
        simp [m2mEigen, m2mVertex_val, ht0]
      · have ht0 : t ≠ (⟨0, by omega⟩ : Fin m) :=
          fun h => ht (congrArg Fin.val h)
        simp [m2mEigen, m2mVertex_val, ht, ht0,
          show (2 * t.val) % 2 = 0 by omega, show 2 * t.val ≠ 1 by omega]
    have e1 : m2mEigen m a b (m2mVertex t 1)
        = if t = (⟨0, by omega⟩ : Fin m)
          then 1 - a * b + (a - b) * ((m : ℝ) - 1)
          else (1 - a) * (1 + b) := by
      by_cases ht : t.val = 0
      · have ht0 : t = (⟨0, by omega⟩ : Fin m) := Fin.ext ht
        simp [m2mEigen, m2mVertex_val, ht0]
      · have ht0 : t ≠ (⟨0, by omega⟩ : Fin m) :=
          fun h => ht (congrArg Fin.val h)
        simp [m2mEigen, m2mVertex_val, ht, ht0]
    rw [e0, e1]
    by_cases ht : t = (⟨0, by omega⟩ : Fin m) <;> simp [ht]
  calc ∏ c : Fin (2 * m), (Polynomial.X
          - Polynomial.C (m2mEigen m a b c))
      = ∏ p : Fin m × Fin 2, (Polynomial.X
          - Polynomial.C (m2mEigen m a b (m2mVertexEquiv m p))) :=
        (Equiv.prod_comp _ _).symm
    _ = ∏ t : Fin m, ∏ e : Fin 2, (Polynomial.X
          - Polynomial.C (m2mEigen m a b (m2mVertex t e))) :=
        Fintype.prod_prod_type _
    _ = ∏ t : Fin m, (if t = (⟨0, by omega⟩ : Fin m) then
            (Polynomial.X
              - Polynomial.C (1 + a * b + (a + b) * ((m : ℝ) - 1)))
            * (Polynomial.X
              - Polynomial.C (1 - a * b + (a - b) * ((m : ℝ) - 1)))
          else
            (Polynomial.X - Polynomial.C ((1 - a) * (1 - b)))
            * (Polynomial.X - Polynomial.C ((1 - a) * (1 + b)))) :=
        Finset.prod_congr rfl (fun t _ => hinner t)
    _ = ((Polynomial.X
              - Polynomial.C (1 + a * b + (a + b) * ((m : ℝ) - 1)))
            * (Polynomial.X
              - Polynomial.C (1 - a * b + (a - b) * ((m : ℝ) - 1))))
          * ((Polynomial.X - Polynomial.C ((1 - a) * (1 - b)))
            * (Polynomial.X - Polynomial.C ((1 - a) * (1 + b))))
            ^ (m - 1) := by
        rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
          (Finset.mem_univ (⟨0, by omega⟩ : Fin m)) _]
        simp only [ite_true]
        congr 1
        refine Eq.trans (Finset.prod_congr
            (g := fun _ : Fin m =>
              (Polynomial.X - Polynomial.C ((1 - a) * (1 - b)))
              * (Polynomial.X - Polynomial.C ((1 - a) * (1 + b))))
            rfl (fun t ht => ?_)) ?_
        · have htne : t ≠ (⟨0, by omega⟩ : Fin m) := by
            simpa using (Finset.mem_sdiff.mp ht).2
          simp only [htne, ite_false]
        · rw [Finset.prod_const]
          congr 1
          simp [Finset.card_sdiff, Fintype.card_fin]
    _ = (Polynomial.X
          - Polynomial.C (1 + a * b + (a + b) * ((m : ℝ) - 1)))
        * (Polynomial.X
          - Polynomial.C (1 - a * b + (a - b) * ((m : ℝ) - 1)))
        * (Polynomial.X - Polynomial.C ((1 - a) * (1 - b))) ^ (m - 1)
        * (Polynomial.X - Polynomial.C ((1 - a) * (1 + b)))
          ^ (m - 1) := by
        rw [mul_pow]
        ring



/-- `m2m_counterexample`: on the curve `a² + (1 - b²) a - 1 = 0`
with `0 < b < a < 1`, the matrix `M_{2m}` is SPD with eigenvalues
`1 + ab + (a+b)(m-1)`, `1 - ab + (a-b)(m-1)`, `(1-a)(1-b)` and
`(1-a)(1+b)` (the last two with multiplicity `m - 1`, as a
characteristic factorization), and for `m ≥ 3` it has no clean
ordering — so Conjecture 1 fails at every even order at least 6
(paper Theorem 5.8, `thm:M2m`). -/
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
  intro m a b hm hcurve hb hba ha1
  have hpos := m2m_posDef hm hb hba ha1
  refine ⟨hpos, m2m_charpoly hm, ?_, ?_, ?_, ?_,
    fun hm3 σ hσ => m2m_no_clean hm3 hcurve hb hba ha1 hpos σ hσ⟩
  · have h := m2mEigen_pos hm hb hba ha1 (⟨0, by omega⟩ : Fin (2 * m))
    simpa [m2mEigen] using h
  · have h := m2mEigen_pos hm hb hba ha1 (⟨1, by omega⟩ : Fin (2 * m))
    simpa [m2mEigen] using h
  · have h := m2mEigen_pos hm hb hba ha1 (⟨2, by omega⟩ : Fin (2 * m))
    simpa [m2mEigen] using h
  · have h := m2mEigen_pos hm hb hba ha1 (⟨3, by omega⟩ : Fin (2 * m))
    simpa [m2mEigen] using h



/-- `M_{2m}` is irreducible when `0 < b < a`: every off-diagonal
entry is `a * b`, `a`, or `b`, all nonzero. -/
theorem m2mMatrix_irreducible {m : ℕ} {a b : ℝ}
    (hb : 0 < b) (hba : b < a) :
    IsIrreducible (m2mMatrix m a b) := by
  intro V₁ V₂ hV₁ hV₂ hdisj _
  obtain ⟨i, hi⟩ := hV₁
  obtain ⟨j, hj⟩ := hV₂
  have hij : i ≠ j := fun h => (Finset.disjoint_left.mp hdisj hi) (h ▸ hj)
  refine ⟨i, hi, j, hj, ?_⟩
  have ha : a ≠ 0 := ne_of_gt (hb.trans hba)
  have hb0 : b ≠ 0 := ne_of_gt hb
  unfold m2mMatrix
  split_ifs with h1 h2 h3
  · exact absurd h1 hij
  · exact mul_ne_zero ha hb0
  · exact ha
  · exact hb0



/-- A concrete point on the curve of Theorem 5.8:
`b = 1/2`, `a = (-3 + √73)/8` satisfies
`a² + (1 - b²)a - 1 = 0` and `0 < b < a < 1`, so the hypothesis of
`m2m_counterexample` is inhabited for every `m`. -/
theorem m2m_curve_instance :
    ∃ a b : ℝ, a ^ 2 + (1 - b ^ 2) * a - 1 = 0 ∧ 0 < b ∧ b < a ∧
      a < 1 := by
  set b : ℝ := 1 / 2 with hbdef
  set a : ℝ := (-3 + Real.sqrt 73) / 8 with hadef
  have hs73 : Real.sqrt 73 ^ 2 = 73 := Real.sq_sqrt (by norm_num)
  have hsqrt_lo : 8 < Real.sqrt 73 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  have hsqrt_hi : Real.sqrt 73 < 9 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 9)]
    norm_num
  have hb : 0 < b := by norm_num [hbdef]
  have hba : b < a := by
    rw [hadef, hbdef]
    linarith
  have ha1 : a < 1 := by
    rw [hadef]
    linarith
  have hsq : (-3 + Real.sqrt 73) ^ 2 = 82 - 6 * Real.sqrt 73 := by
    calc (-3 + Real.sqrt 73) ^ 2
        = 9 - 6 * Real.sqrt 73 + Real.sqrt 73 ^ 2 := by ring
      _ = 82 - 6 * Real.sqrt 73 := by rw [hs73]; ring
  have ha2 : a ^ 2 = (82 - 6 * Real.sqrt 73) / 64 := by
    rw [hadef, div_pow, hsq]
    norm_num
  have hcurve : a ^ 2 + (1 - b ^ 2) * a - 1 = 0 := by
    rw [ha2, hadef, hbdef]
    ring
  exact ⟨a, b, hcurve, hb, hba, ha1⟩



/-- Conjecture 1 fails at every even order `2m ≥ 6` (paper
Theorem 5.8, `thm:M2m`): for each `m ≥ 3` the matrix `M_{2m}` at
the curve point of `m2m_curve_instance` is irreducible and
positive definite with no clean ordering. -/
theorem m2m_counterexample_all_orders (m : ℕ) (hm : 3 ≤ m) :
    ∃ A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ,
      A.PosDef ∧ IsIrreducible A ∧
        ∀ σ : List (Fin (2 * m)), IsOrdering σ →
          ¬ IsCleanOrdering A σ := by
  obtain ⟨a, b, hcurve, hb, hba, ha1⟩ := m2m_curve_instance
  obtain ⟨hpos, -, -, -, -, -, hnoclean⟩ :=
    m2m_counterexample m a b (by omega) hcurve hb hba ha1
  exact ⟨m2mMatrix m a b, hpos, m2mMatrix_irreducible hb hba,
    hnoclean hm⟩



/-- The fill-graph conjecture (paper Conjecture 2.27, `conj:1`) is
false, by `M₆` at the curve point of `m2m_curve_instance` (paper
Theorem 5.8, `thm:M2m`). -/
theorem fill_graph_conjecture_refuted : ¬ fill_graph_conjecture := by
  intro h
  obtain ⟨A, hpos, hirr, hnoclean⟩ :=
    m2m_counterexample_all_orders 3 (by norm_num)
  obtain ⟨σ, hσord, hclean⟩ := h A hpos hirr
  exact hnoclean σ hσord hclean

end CholeskyCancellations

/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Section_5_EvenCounterexamplesAndOrderFour.F_M2mPosDef

/-! # The parameter curve is a one-parameter family (paper Section 5)

The root `curveRoot b = α(B)` of `f(A) = A² + (1 - B²) A - 1` (paper Remark 5.9,
`rem:curve-family`): it lies on the curve (4) with `B < α(B) < 1`, it is the unique positive
root, the admissible pairs of (4) are exactly the `(α(B), B)` with `0 < B < 1`, the instance
`α(1/2) = (-3 + √73)/8`, Theorem 5.8 at every point of the family, and the two excluded
endpoints (`B = 0` breaks the completeness of `G_{M2m}`; `B → 1` forces `A → 1` and
`λ₃ = (1 - A)(1 - B) → 0`). Not formalized: the measure-zero remark and the decimal
approximations `A ≈ 0.693`, `AB ≈ 0.3465`.
-/

open scoped Matrix

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as the Section 2 files;
concrete matrices are on `Fin 4` and `Fin (2 * m)` with pair/parity read from `Finset` levels
and `Fin.val` division as in the paper's `P_k = {2k, 2k+1}` indexing. (Plain comment: a
docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- `curveRoot b`: the root `α(B) = (-(1 - B²) + √((1 - B²)² + 4)) / 2` of
`f(A) = A² + (1 - B²) A - 1`, regarded as a function of `B` (not a product) (paper
Remark 5.9, `rem:curve-family`). -/
noncomputable def curveRoot (b : ℝ) : ℝ :=
  (-(1 - b ^ 2) + Real.sqrt ((1 - b ^ 2) ^ 2 + 4)) / 2



/-- The radical in `curveRoot` squares to its radicand `(1 - B²)² + 4 > 0` (paper Remark 5.9,
`rem:curve-family`). -/
theorem curveRoot_radical_sq (b : ℝ) :
    Real.sqrt ((1 - b ^ 2) ^ 2 + 4) ^ 2 = (1 - b ^ 2) ^ 2 + 4 :=
  Real.sq_sqrt (by positivity)



/-- `α(B)` is a root of `f(A) = A² + (1 - B²) A - 1`, for every real `B` (the quadratic
formula, paper Remark 5.9, `rem:curve-family`). -/
theorem curveRoot_isRoot (b : ℝ) :
    curveRoot b ^ 2 + (1 - b ^ 2) * curveRoot b - 1 = 0 := by
  have hs := curveRoot_radical_sq b
  unfold curveRoot
  linear_combination hs / 4



/-- `α(B) > 0`, for every real `B`: the radical `√((1 - B²)² + 4)` exceeds `1 - B²` (paper
Remark 5.9, `rem:curve-family`). -/
theorem curveRoot_pos (b : ℝ) : 0 < curveRoot b := by
  have hs := curveRoot_radical_sq b
  have hs0 := Real.sqrt_nonneg ((1 - b ^ 2) ^ 2 + 4)
  unfold curveRoot
  nlinarith [sq_nonneg (Real.sqrt ((1 - b ^ 2) ^ 2 + 4) - (1 - b ^ 2))]



/-- For `B ∈ (0, 1)`, `f(A) = A² + (1 - B²) A - 1` is strictly increasing on `A > 0` (paper
Remark 5.9, `rem:curve-family`). -/
theorem curveRoot_poly_strictMonoOn {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    StrictMonoOn (fun x : ℝ => x ^ 2 + (1 - b ^ 2) * x - 1) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  have hc : 0 < 1 - b ^ 2 := by nlinarith
  have hpos : 0 < (y - x) * (y + x + (1 - b ^ 2)) :=
    mul_pos (by linarith) (by linarith)
  simp only
  nlinarith [hpos]



/-- The sign of `f` at positive arguments: for `x > 0`, `x < α(B)` if and only if
`f(x) = x² + (1 - B²) x - 1 < 0`, since `f` is strictly increasing on `A > 0` and vanishes at
`α(B)` (paper Remark 5.9, `rem:curve-family`). -/
theorem curveRoot_lt_iff {b x : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hx : 0 < x) :
    x < curveRoot b ↔ x ^ 2 + (1 - b ^ 2) * x - 1 < 0 := by
  have h := (curveRoot_poly_strictMonoOn hb0 hb1).lt_iff_lt
    (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr (curveRoot_pos b))
  simp only [curveRoot_isRoot] at h
  exact h.symm



/-- The value of `f` at `B` itself: `f(B) = B² + (1 - B²) B - 1 = -(B - 1)²(B + 1)` (paper
Remark 5.9, `rem:curve-family`). -/
theorem curveRoot_poly_self (b : ℝ) :
    b ^ 2 + (1 - b ^ 2) * b - 1 = -((b - 1) ^ 2 * (b + 1)) := by
  ring



/-- `B < α(B)` automatically for `B ∈ (0, 1)`: `f(B) = -(B - 1)²(B + 1) < 0`, so
`curveRoot_lt_iff` at `x = B` applies (paper Remark 5.9, `rem:curve-family`). -/
theorem curveRoot_gt {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) : b < curveRoot b := by
  rw [curveRoot_lt_iff hb0 hb1 hb0, curveRoot_poly_self]
  have h1 : 0 < 1 - b := by linarith
  have h2 : 0 < (1 - b) ^ 2 * (b + 1) := by positivity
  nlinarith [h2]



/-- `α(B) < 1` for `B ∈ (0, 1)`: `f(α(B)) = 0 < 1 - B² = f(1)` and `f` is strictly increasing
on `A > 0` (paper Remark 5.9, `rem:curve-family`). -/
theorem curveRoot_lt_one {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) : curveRoot b < 1 := by
  have h := (curveRoot_poly_strictMonoOn hb0 hb1).lt_iff_lt
    (Set.mem_Ioi.mpr (curveRoot_pos b)) (Set.mem_Ioi.mpr one_pos)
  simp only [curveRoot_isRoot] at h
  apply h.mp
  nlinarith



/-- `curveRoot_spec`: for `B ∈ (0, 1)` the point `(α(B), B)` lies on the curve
`A² + (1 - B²) A - 1 = 0` of hypothesis (4) and satisfies `B < α(B) < 1` (paper Remark 5.9,
`rem:curve-family`). -/
theorem curveRoot_spec {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    curveRoot b ^ 2 + (1 - b ^ 2) * curveRoot b - 1 = 0 ∧ b < curveRoot b ∧ curveRoot b < 1 :=
  ⟨curveRoot_isRoot b, curveRoot_gt hb0 hb1, curveRoot_lt_one hb0 hb1⟩



/-- `eq_curveRoot`: for `B ∈ (0, 1)`, `α(B)` is the only positive root of
`f(A) = A² + (1 - B²) A - 1` — stronger than uniqueness in `(0, 1)`, since `f` is strictly
increasing on `A > 0` (paper Remark 5.9, `rem:curve-family`). -/
theorem eq_curveRoot {a b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (ha0 : 0 < a)
    (h : a ^ 2 + (1 - b ^ 2) * a - 1 = 0) : a = curveRoot b :=
  (curveRoot_poly_strictMonoOn hb0 hb1).injOn (Set.mem_Ioi.mpr ha0)
    (Set.mem_Ioi.mpr (curveRoot_pos b)) (by simp only [h, curveRoot_isRoot])



/-- `curve_admissible_iff`: the admissible parameters of hypothesis (4) are exactly the pairs
`(α(B), B)` with `0 < B < 1`; the inequalities `0 < B < A < 1` of (4) are consequences of the
curve equation rather than extra assumptions (paper Remark 5.9, `rem:curve-family`). -/
theorem curve_admissible_iff (a b : ℝ) :
    (a ^ 2 + (1 - b ^ 2) * a - 1 = 0 ∧ 0 < b ∧ b < a ∧ a < 1) ↔
      (0 < b ∧ b < 1 ∧ a = curveRoot b) := by
  constructor
  · rintro ⟨h, hb0, hba, ha1⟩
    have hb1 : b < 1 := hba.trans ha1
    exact ⟨hb0, hb1, eq_curveRoot hb0 hb1 (hb0.trans hba) h⟩
  · rintro ⟨hb0, hb1, rfl⟩
    exact ⟨curveRoot_isRoot b, hb0, curveRoot_gt hb0 hb1, curveRoot_lt_one hb0 hb1⟩



/-- `curveRoot_half`: the instance `B = 1/2` used for the explicit verification of
Appendices A and E has `A = α(1/2) = (-3 + √73)/8` (paper Remark 5.9, `rem:curve-family`; it is
the witness of `m2m_curve_instance`). -/
theorem curveRoot_half : curveRoot (1 / 2) = (-3 + Real.sqrt 73) / 8 := by
  have hrad : (1 - (1 / 2 : ℝ) ^ 2) ^ 2 + 4 = 73 / 4 ^ 2 := by norm_num
  have hsqrt : Real.sqrt ((1 - (1 / 2 : ℝ) ^ 2) ^ 2 + 4) = Real.sqrt 73 / 4 := by
    rw [hrad, Real.sqrt_div' 73 (by norm_num : (0 : ℝ) ≤ 4 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  unfold curveRoot
  rw [hsqrt]
  ring



/-- `m2m_family_counterexample`: Theorem 5.8 along the whole family — for every `B ∈ (0, 1)`
and every `m ≥ 3`, the matrix `M_{2m}` at `(α(B), B)` is SPD, irreducible, and has no clean
ordering, so each even order `2m ≥ 6` carries a one-parameter family of counterexamples
(paper Remark 5.9, `rem:curve-family`, with paper Theorem 5.8, `thm:M2m`). -/
theorem m2m_family_counterexample {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) {m : ℕ} (hm : 3 ≤ m) :
    (m2mMatrix m (curveRoot b) b).PosDef ∧ IsIrreducible (m2mMatrix m (curveRoot b) b) ∧
      ∀ σ : List (Fin (2 * m)), IsOrdering σ →
        ¬ IsCleanOrdering (m2mMatrix m (curveRoot b) b) σ := by
  obtain ⟨hcurve, hba, ha1⟩ := curveRoot_spec hb0 hb1
  obtain ⟨hpos, -, -, -, -, -, hnoclean⟩ :=
    m2m_counterexample m (curveRoot b) b (by omega) hcurve hb0 hba ha1
  exact ⟨hpos, m2mMatrix_irreducible hb0 hba, hnoclean hm⟩



/-- At `B = 0` the opposite-parity cross entries of `M_{2m}` vanish: for `x`, `y` in different
pairs and of opposite parity, `(M_{2m})_{xy} = B = 0` (paper Remark 5.9, `rem:curve-family`). -/
theorem curveRoot_m2m_opposite_parity_b_zero {m : ℕ} {a : ℝ} {x y : Fin (2 * m)}
    (hdiv : x.val / 2 ≠ y.val / 2) (hpar : x.val % 2 ≠ y.val % 2) :
    m2mMatrix m a 0 x y = 0 := by
  rw [m2m_apply_cross hdiv, ite_eq_right hpar]



/-- `m2m_pattern_ne_top_of_b_eq_zero`: the endpoint `B = 0` is excluded for good reason — it
annihilates the opposite-parity entries, so for `m ≥ 2` the pattern graph `G_{M2m}` is no
longer complete (the vertices `0 ∈ P₀` and `3 ∈ P₁` become non-adjacent) (paper Remark 5.9,
`rem:curve-family`). -/
theorem m2m_pattern_ne_top_of_b_eq_zero {m : ℕ} (hm : 2 ≤ m) (a : ℝ) :
    patternGraph (m2mMatrix m a 0) ≠ ⊤ := by
  intro h
  set x : Fin (2 * m) := ⟨0, by omega⟩ with hx
  set y : Fin (2 * m) := ⟨3, by omega⟩ with hy
  have hxy : x ≠ y := by
    intro hh
    have hv := congrArg Fin.val hh
    simp [hx, hy] at hv
  have hadj : (patternGraph (m2mMatrix m a 0)).Adj x y := by
    rw [h]
    exact hxy
  have hdiv : x.val / 2 ≠ y.val / 2 := by simp [hx, hy]
  have hpar : x.val % 2 ≠ y.val % 2 := by simp [hx, hy]
  have h1 : m2mMatrix m a 0 x y = 0 := curveRoot_m2m_opposite_parity_b_zero hdiv hpar
  have h2 : m2mMatrix m a 0 y x = 0 :=
    curveRoot_m2m_opposite_parity_b_zero (Ne.symm hdiv) (Ne.symm hpar)
  simp only [patternGraph, SimpleGraph.fromRel_adj] at hadj
  rcases hadj.2 with h' | h'
  · exact h' h1
  · exact h' h2



/-- `curveRoot` is continuous, as a composite of polynomials and `Real.sqrt` (paper
Remark 5.9, `rem:curve-family`: the limit `B → 1`). -/
theorem curveRoot_continuous : Continuous curveRoot := by
  unfold curveRoot
  fun_prop



/-- At the excluded endpoint `B = 1` the formula gives `α(1) = (0 + √4)/2 = 1` (paper
Remark 5.9, `rem:curve-family`). -/
theorem curveRoot_one : curveRoot 1 = 1 := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  unfold curveRoot
  norm_num [h4]



/-- `tendsto_curveRoot_one`: `B → 1⁻` forces `A = α(B) → 1` (paper Remark 5.9,
`rem:curve-family`). -/
theorem tendsto_curveRoot_one :
    Filter.Tendsto curveRoot (nhdsWithin 1 (Set.Iio 1)) (nhds 1) :=
  (curveRoot_continuous.tendsto' 1 1 curveRoot_one).mono_left nhdsWithin_le_nhds



/-- `tendsto_m2m_lambda3`: along the family, as `B → 1⁻` the eigenvalue
`λ₃ = (1 - A)(1 - B)` of `M_{2m}` (the multiplicity-`(m - 1)` eigenvalue `(1 - a) * (1 - b)` of
`m2m_counterexample`) tends to `0`, so positive definiteness degenerates at the endpoint
(paper Remark 5.9, `rem:curve-family`). -/
theorem tendsto_m2m_lambda3 :
    Filter.Tendsto (fun b => (1 - curveRoot b) * (1 - b)) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  have hc : Continuous (fun b => (1 - curveRoot b) * (1 - b)) := by
    have h := curveRoot_continuous
    fun_prop
  exact (hc.tendsto' 1 0 (by simp [curveRoot_one])).mono_left nhdsWithin_le_nhds

end CholeskyCancellations

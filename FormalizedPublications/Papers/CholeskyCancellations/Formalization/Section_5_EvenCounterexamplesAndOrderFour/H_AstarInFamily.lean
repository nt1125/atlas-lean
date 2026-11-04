/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Section_5_EvenCounterexamplesAndOrderFour.G_ParameterCurve

/-! # `A*` is the order-four member of the `M_{2m}` family (paper Section 5)

The matrix `A*` of Theorem 5.1 (`astar`), normalised to unit diagonal, relabeled by
`(0, 3, 1, 2)` and conjugated by `D = diag(-1, 1, 1, 1)`, is the member `M₄` of the `M_{2m}`
family with `m = 2`, `A = B = 1/2` (paper Remark 5.10, `rem:astar-family`). Conjugation by a
diagonal sign matrix (`signConj`) preserves positive definiteness, the pattern graph, every
Schur entry up to sign, every log-magnitude `t⁽ˢ⁾_{jk}`, clean orderings, and clean first Schur
complements — the entire cancellation structure. The member lies off the curve (4).
-/

open scoped Matrix

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as the Section 2 files;
concrete matrices are on `Fin 4` and `Fin (2 * m)` with pair/parity read from `Finset` levels
and `Fin.val` division as in the paper's `P_k = {2k, 2k+1}` indexing. (Plain comment: a
docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- `astarSign`: the diagonal `d = (-1, 1, 1, 1)` of the sign matrix `D = diag(-1, 1, 1, 1)`
that conjugates `A*` into the `M_{2m}` family (paper Remark 5.10, `rem:astar-family`). -/
def astarSign : Fin 4 → ℝ := ![-1, 1, 1, 1]



/-- `astarRelabel`: the relabeling `(0, 3, 1, 2)` — listing the vertices of `A*` in the order
`0, 3, 1, 2` gives the vertices `0, 1, 2, 3` of `M₄`, so vertex `i` of `A*` is vertex
`astarRelabel i` of `M₄`; the pairs `{0, 3}`, `{1, 2}` of `A*` (the partners of
`astarPartner`) become the pairs `P₀ = {0, 1}`, `P₁ = {2, 3}` (paper Remark 5.10,
`rem:astar-family`). -/
def astarRelabel : Fin 4 → Fin (2 * 2) := ![0, 2, 3, 1]



/-- `astar_div_four_eq_m2m`: `A*` normalised to unit diagonal (its diagonal is `4`, so the
normalisation is `A*/4`) is, entrywise, the member `M₄ = m2mMatrix 2 (1/2) (1/2)` of the
family (`m = 2`, `A = B = 1/2`, `AB = 1/4`) relabeled by `τ = astarRelabel` and conjugated by
`D = diag(astarSign)`: `(A*/4)ᵢⱼ = dᵢ dⱼ (M₄)_{τi,τj}`. In particular `|r₀₃| = |r₁₂| = 1/4`
(the in-pair entries `AB`) and the four cross entries have modulus `1/2` (paper Remark 5.10,
`rem:astar-family`). -/
theorem astar_div_four_eq_m2m (i j : Fin 4) :
    astar i j / 4 =
      astarSign i * astarSign j *
        m2mMatrix 2 (1 / 2) (1 / 2) (astarRelabel i) (astarRelabel j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [astar, astarSign, astarRelabel, m2mMatrix]



/-- `astar_member_off_curve`: at the parameters `A = B = 1/2` of this member,
`A² + (1 - B²) A - 1 = -3/8 ≠ 0`, so `M₄`, and with it `A*`, lies off the curve (4): the
no-clean-ordering half of Theorem 5.8 (`m2m_no_clean`, which cancels the opposite-parity cross
entries after a partnered pair of pivots by the curve equation, and needs a third pair,
`m ≥ 3`) does not reach it. The paper reads this as why `M₄` fails the First-Schur Conjecture
(Conjecture 2.26, `conj:2`) only. At order four the curve is in fact not decisive: every
irreducible SPD matrix of order at most four has a clean ordering (`clean_of_order_le_four`,
Theorem 5.2), on the curve or off it. Consistently with `astar_counts`, no ordering of `A*` has
a clean first Schur complement, yet `A*` has exactly eight clean orderings — properties the
sign conjugation preserves (`firstSchurClean_signConj`, `isCleanOrdering_signConj`) and the
relabeling merely transports (paper Remark 5.10, `rem:astar-family`). -/
theorem astar_member_off_curve :
    (1 / 2 : ℝ) ^ 2 + (1 - (1 / 2) ^ 2) * (1 / 2) - 1 = -3 / 8 := by
  norm_num



/-- Conjugation by a diagonal sign matrix, `D A D` with `D = diag d` (paper Remark 5.10,
`rem:astar-family`, where `D = diag(-1, 1, 1, 1)`). -/
def signConj (d : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => d i * d j * A i j



/-- The entries of `D A D` are `dᵢ dⱼ Aᵢⱼ` (paper Remark 5.10, `rem:astar-family`). -/
theorem signConj_apply (d : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    signConj d A i j = d i * d j * A i j :=
  rfl



/-- The matrix form of paper Remark 5.10 (`rem:astar-family`): `A*/4 = D (M₄ ∘ τ) D`, the
conjugation by `D = diag(astarSign)` of `M₄ = m2mMatrix 2 (1/2) (1/2)` relabeled by
`τ = astarRelabel` (entrywise, this is `astar_div_four_eq_m2m`). -/
theorem astar_div_four_eq_signConj_submatrix :
    (1 / 4 : ℝ) • astar =
      signConj astarSign
        ((m2mMatrix 2 (1 / 2) (1 / 2)).submatrix astarRelabel astarRelabel) := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, signConj_apply, Matrix.submatrix_apply,
    ← astar_div_four_eq_m2m]
  ring



/-- The entries of `astarSign` are signs `±1`, so the `signConj` lemmas below apply to
`D = diag(-1, 1, 1, 1)` (paper Remark 5.10, `rem:astar-family`). -/
theorem astarSign_sign (i : Fin 4) : astarSign i = 1 ∨ astarSign i = -1 := by
  fin_cases i <;> simp [astarSign]



/-- A sign `dᵢ = ±1` is nonzero (paper Remark 5.10, `rem:astar-family`). -/
theorem signConj_ne_zero {d : Fin n → ℝ} (hd : ∀ i, d i = 1 ∨ d i = -1) (i : Fin n) :
    d i ≠ 0 := by
  rcases hd i with h | h <;> rw [h] <;> norm_num



/-- Two signs neither create nor destroy a zero: `dⱼ dₖ x ≠ 0 ↔ x ≠ 0` (paper Remark 5.10,
`rem:astar-family`). -/
theorem signConj_mul_ne_zero_iff {d : Fin n → ℝ} (hd : ∀ i, d i = 1 ∨ d i = -1)
    (j k : Fin n) (x : ℝ) : d j * d k * x ≠ 0 ↔ x ≠ 0 := by
  simp [signConj_ne_zero hd j, signConj_ne_zero hd k]



/-- `D A D = Dᴴ A D` for `D = diag d`, a real diagonal matrix being self-adjoint (paper
Remark 5.10, `rem:astar-family`). -/
theorem signConj_eq_conjTranspose_mul_mul (d : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    signConj d A = (Matrix.diagonal d)ᴴ * A * Matrix.diagonal d := by
  ext i j
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, signConj_apply,
    Pi.star_apply, star_trivial]
  ring



/-- `signConj_posDef`: conjugation by a diagonal sign matrix preserves positive definiteness,
as `D A D = Dᴴ A D` with `D` invertible (paper Remark 5.10, `rem:astar-family`). -/
theorem signConj_posDef {d : Fin n → ℝ} (hd : ∀ i, d i = 1 ∨ d i = -1)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) : (signConj d A).PosDef := by
  rw [signConj_eq_conjTranspose_mul_mul]
  refine hA.conjTranspose_mul_mul_same ?_
  intro x y hxy
  funext i
  have hi := congr_fun hxy i
  rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal] at hi
  exact mul_left_cancel₀ (signConj_ne_zero hd i) hi



/-- `schurEntry_signConj`: Schur complements commute with sign conjugation,
`(DAD)/(DAD)_S = D_R (A/A_S) D_R` entrywise: `((DAD)/(DAD)_S)ⱼₖ = dⱼ dₖ (A/A_S)ⱼₖ`. By
induction on `S` through the quotient property (paper Lemma 2.4, `lem:quotient`, as
`schur_quotient`): in the pivot update the pivot's sign enters squared; off the survivors both
sides are the junk value `0` (paper Remark 5.10, `rem:astar-family`). -/
theorem schurEntry_signConj {d : Fin n → ℝ} (hd : ∀ i, d i = 1 ∨ d i = -1)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (S : Finset (Fin n)) (j k : Fin n) :
    schurEntry (signConj d A) S j k = d j * d k * schurEntry A S j k := by
  have hDA := signConj_posDef hd hA
  induction S using Finset.induction_on generalizing j k with
  | empty => rw [schurEntry_empty, schurEntry_empty, signConj_apply]
  | insert v S hv ih =>
    by_cases hj : j ∈ insert v S
    · have hj' : j ∉ (insert v S)ᶜ := fun h => Finset.mem_compl.mp h hj
      rw [schurEntry, schurEntry, dite_eq_right hj', dite_eq_right hj', mul_zero]
    by_cases hk : k ∈ insert v S
    · have hk' : k ∉ (insert v S)ᶜ := fun h => Finset.mem_compl.mp h hk
      have hj' : j ∈ (insert v S)ᶜ := Finset.mem_compl.mpr hj
      rw [schurEntry, schurEntry, dite_eq_left hj', dite_eq_left hj', dite_eq_right hk',
        dite_eq_right hk', mul_zero]
    rw [schur_quotient hDA S v hv j k hj hk, schur_quotient hA S v hv j k hj hk]
    simp only [pivotEntry, ih]
    rcases hd v with h | h <;> rw [h] <;> ring



/-- `patternGraph_signConj`: conjugation by a diagonal sign matrix leaves the pattern graph
unchanged, as `dᵢ dⱼ Aᵢⱼ ≠ 0 ↔ Aᵢⱼ ≠ 0` (paper Remark 5.10, `rem:astar-family`). -/
theorem patternGraph_signConj {d : Fin n → ℝ} (hd : ∀ i, d i = 1 ∨ d i = -1)
    (A : Matrix (Fin n) (Fin n) ℝ) : patternGraph (signConj d A) = patternGraph A := by
  ext i j
  simp only [patternGraph, SimpleGraph.fromRel_adj, signConj_apply,
    signConj_mul_ne_zero_iff hd]



/-- `logMag_signConj`: conjugation by a diagonal sign matrix leaves every log-magnitude
`t⁽ˢ⁾_{jk} = -log |r⁽ˢ⁾_{jk}|` unchanged: the partial correlation only changes by the sign
`dⱼ dₖ` (paper Remark 5.10, `rem:astar-family`). -/
theorem logMag_signConj {d : Fin n → ℝ} (hd : ∀ i, d i = 1 ∨ d i = -1)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (S : Finset (Fin n)) (j k : Fin n) :
    logMag (signConj d A) S j k = logMag A S j k := by
  unfold logMag partialCorr
  simp only [schurEntry_signConj hd hA]
  rcases hd j with hj | hj <;> rcases hd k with hk | hk <;> simp [hj, hk, neg_div]



/-- `isCleanOrdering_signConj`: an ordering is clean for `D A D` iff it is clean for `A` —
sign conjugation keeps the fill graph (it keeps the pattern graph) and keeps every committed
entry nonzero exactly when it was (paper Remark 5.10, `rem:astar-family`). -/
theorem isCleanOrdering_signConj {d : Fin n → ℝ} (hd : ∀ i, d i = 1 ∨ d i = -1)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (σ : List (Fin n)) :
    IsCleanOrdering (signConj d A) σ ↔ IsCleanOrdering A σ := by
  have hfill : fillGraph (signConj d A) σ = fillGraph A σ := by
    simp only [fillGraph, patternGraph_signConj hd A]
  simp only [IsCleanOrdering, PredictedNonzero, hfill, schurEntry_signConj hd hA,
    signConj_mul_ne_zero_iff hd]



/-- `firstSchurClean_signConj`: an ordering has a clean first Schur complement for `D A D` iff
it has one for `A` — the game graph after the first pivot only reads the pattern graph, and
`schurEntry_signConj` keeps every zero (paper Remark 5.10, `rem:astar-family`). -/
theorem firstSchurClean_signConj {d : Fin n → ℝ} (hd : ∀ i, d i = 1 ∨ d i = -1)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (σ : List (Fin n)) :
    FirstSchurClean (signConj d A) σ ↔ FirstSchurClean A σ := by
  simp only [FirstSchurClean, patternGraph_signConj hd A, schurEntry_signConj hd hA,
    signConj_mul_ne_zero_iff hd]

end CholeskyCancellations

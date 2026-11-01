/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Schur complement (paper Section 2)

Schur complements at a level `S`: the survivor index type, `schurEntry`, `pivotEntry`, and the basic SPD facts (Schur complements of SPD matrices stay SPD; `2 × 2` minors). Split from `Defs.lean`.
-/

open scoped Matrix

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): vertices `Fin n`, SPD = `Matrix.PosDef`, levels `Finset (Fin n)`, pivot-order list orderings, Schur entries through `schurEntry` only. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}


/-- The survivor index type at level `S`: `R = V \ S`
(paper Definition 2.2). -/
abbrev Survivors (S : Finset (Fin n)) : Type :=
  ↥Sᶜ



/-- The index equivalence `S ⊕ (V \ S) ≃ V` used to read `A` in
`2×2` block form for Schur complement arguments. -/
noncomputable def sumComplEquiv (S : Finset (Fin n)) :
    (↥S ⊕ ↥Sᶜ) ≃ Fin n where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun i := if h : i ∈ S then Sum.inl ⟨i, h⟩
    else Sum.inr ⟨i, Finset.mem_compl.mpr h⟩
  left_inv x := by
    cases x with
    | inl a => simp [a.2]
    | inr a => simp [Finset.mem_compl.mp a.2]
  right_inv i := by by_cases h : i ∈ S <;> simp [h]



/-- `schurSet A S`: the Schur complement `A/A_S = A_RR - A_RS A_SS⁻¹ A_SR`
on the survivors `R = V \ S` (paper Definition 2.2, `def:spd-schur`).
Total by junk values, like `Matrix.inv`: if `A_SS` is singular the
inverse is `0`. -/
noncomputable def schurSet (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    Matrix (Survivors S) (Survivors S) ℝ :=
  let aRR : Matrix (Survivors S) (Survivors S) ℝ :=
    A.submatrix Subtype.val Subtype.val
  let aRS : Matrix (Survivors S) ↥S ℝ :=
    A.submatrix Subtype.val Subtype.val
  let aSS : Matrix ↥S ↥S ℝ :=
    A.submatrix Subtype.val Subtype.val
  let aSR : Matrix ↥S (Survivors S) ℝ :=
    A.submatrix Subtype.val Subtype.val
  aRR - aRS * aSS⁻¹ * aSR



/-- `schurEntry A S j k`: the entry `(A/A_S)_{jk}` (paper
Definition 2.2), read at plain vertices. Outside the survivors the
value is the junk value `0`; every use is guarded by `j ∉ S`, `k ∉ S`. -/
noncomputable def schurEntry (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (j k : Fin n) : ℝ :=
  if hj : j ∈ Sᶜ then
    if hk : k ∈ Sᶜ then schurSet A S ⟨j, hj⟩ ⟨k, hk⟩ else 0
  else 0



/-- An SPD matrix is entrywise symmetric (from Mathlib's
`Matrix.PosDef.isHermitian`, at paper Definition 2.1's matrices). -/
theorem posDef_apply_comm (hA : A.PosDef) (i j : Fin n) :
    A i j = A j i := by
  have h := hA.isHermitian.apply i j
  simpa using h.symm



/-- Schur complements of an SPD matrix are SPD (the hard half of
paper Proposition 2.3; via the block form of `A` over
`sumComplEquiv S` and Mathlib's `Matrix.schur_complement_eq₁₁`
completing-the-square identity, as in the proof of
`Matrix.PosDef.fromBlocks₁₁`). -/
theorem schurSet_posDef (hA : A.PosDef) (S : Finset (Fin n)) :
    (schurSet A S).PosDef := by
  classical
  have hinjS : Function.Injective (Subtype.val : ↥S → Fin n) :=
    Subtype.val_injective
  have hSS : (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val).PosDef :=
    hA.submatrix hinjS
  let _ := hSS.isUnit.invertible
  have hRS : A.submatrix (Subtype.val : ↥Sᶜ → Fin n) Subtype.val
      = (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val)ᴴ := by
    ext r s
    simp [Matrix.conjTranspose, Matrix.transpose, Matrix.submatrix,
      posDef_apply_comm hA]
  have hherm : (schurSet A S).IsHermitian := by
    change (A.submatrix (Subtype.val : ↥Sᶜ → Fin n) Subtype.val
      - A.submatrix (Subtype.val : ↥Sᶜ → Fin n) Subtype.val
        * (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val)⁻¹
        * A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val).IsHermitian
    rw [hRS]
    exact (hA.isHermitian.submatrix _).sub
      (Matrix.isHermitian_conjTranspose_mul_mul _ hSS.isHermitian.inv)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm ?_
  intro x hx
  have hfb : (Matrix.fromBlocks
      (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val)
      (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val)
      (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val)ᴴ
      (A.submatrix (Subtype.val : ↥Sᶜ → Fin n) Subtype.val)).PosDef := by
    have hAe : (A.submatrix (sumComplEquiv S) (sumComplEquiv S)).PosDef :=
      hA.submatrix (sumComplEquiv S).injective
    convert hAe using 1
    ext p q
    cases p with
    | inl p =>
        cases q with
        | inl q =>
            simp [Matrix.fromBlocks_apply₁₁, Matrix.submatrix,
              sumComplEquiv]
        | inr q =>
            simp [Matrix.fromBlocks_apply₁₂, Matrix.submatrix,
              sumComplEquiv]
    | inr p =>
        cases q with
        | inl q =>
            simp [Matrix.fromBlocks_apply₂₁, Matrix.submatrix,
              Matrix.conjTranspose, Matrix.transpose, sumComplEquiv,
              posDef_apply_comm hA]
        | inr q =>
            simp [Matrix.fromBlocks_apply₂₂, Matrix.submatrix,
              sumComplEquiv]
  have hw : (Sum.elim (-(((A.submatrix (Subtype.val : ↥S → Fin n)
      Subtype.val)⁻¹
      * A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val) *ᵥ x)) x)
      ≠ 0 := by
    intro h
    apply hx
    funext i
    have hi := congr_fun h (Sum.inr i)
    simpa using hi
  have hpos := hfb.dotProduct_mulVec_pos hw
  rw [Matrix.dotProduct_mulVec,
    Matrix.schur_complement_eq₁₁ _ _ _ _ hSS.isHermitian] at hpos
  simp only [neg_add_cancel, dotProduct_zero, zero_add] at hpos
  rw [← Matrix.dotProduct_mulVec] at hpos
  convert hpos using 2
  change (A.submatrix (Subtype.val : ↥Sᶜ → Fin n) Subtype.val
    - A.submatrix (Subtype.val : ↥Sᶜ → Fin n) Subtype.val
      * (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val)⁻¹
      * A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val) *ᵥ x = _
  rw [hRS]



/-- Schur complements of an SPD matrix exist and stay SPD (paper
Proposition 2.3, `prop:schur-basic`). The paper's
order-independence is definitional here: `schurSet` mentions no
ordering of `S`. -/
theorem schur_basic (hA : A.PosDef) (S : Finset (Fin n)) :
    (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val).PosDef ∧
      (schurSet A S).PosDef :=
  ⟨hA.submatrix Subtype.val_injective, schurSet_posDef hA S⟩



/-- `pivotEntry A S p j k`: the rank-one update value
`M_{jk} - M_{jp} M_{kp} / M_{pp}` for `M = A/A_S` (paper
Definition 2.6, `def:pivot`); `M_{jp}`, `M_{kp}` are its legs and
`M_{pp}` its pivot value. -/
noncomputable def pivotEntry (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p j k : Fin n) : ℝ :=
  schurEntry A S j k
    - schurEntry A S j p * schurEntry A S k p / schurEntry A S p p



/-- The Schur complement at the empty level is `A` itself, reindexed
(paper Definition 2.2 at `S = ∅`: the correction sums over the empty
index type). -/
theorem schurSet_empty : schurSet A (∅ : Finset (Fin n))
    = A.submatrix (Subtype.val : Survivors (∅ : Finset (Fin n)) → Fin n)
        Subtype.val := by
  ext x y
  simp only [schurSet, Matrix.sub_apply, Matrix.mul_apply]
  simp



/-- Entries at the empty level are entries of `A` (paper
Definition 2.2: `S⁽⁰⁾ = A`). -/
theorem schurEntry_empty (j k : Fin n) :
    schurEntry A (∅ : Finset (Fin n)) j k = A j k := by
  simp [schurEntry, schurSet_empty, Matrix.submatrix]



/-- Every `2×2` principal minor of an SPD matrix is positive
(the determinant fact behind paper Section 3's first family). -/
theorem posDef_two_mul_sub_pos {ι : Type*} [Finite ι]
    {M : Matrix ι ι ℝ} (hM : M.PosDef) {i j : ι}
    (hij : i ≠ j) : 0 < M i i * M j j - M i j * M j i := by
  have := Fintype.ofFinite ι
  classical
  have hinj : Function.Injective ![i, j] := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  have hB := (hM.submatrix hinj).det_pos
  rwa [Matrix.det_fin_two] at hB



/-- A survivor entry of `A/A_S` is the corresponding matrix entry of
`schurSet A S` (unfolding the junk convention of `schurEntry`). -/
theorem schurEntry_eq (S : Finset (Fin n)) {j k : Fin n}
    (hj : j ∉ S) (hk : k ∉ S) :
    schurEntry A S j k = schurSet A S ⟨j, Finset.mem_compl.mpr hj⟩
      ⟨k, Finset.mem_compl.mpr hk⟩ := by
  simp [schurEntry, hj, hk]



/-- Schur complement entries of an SPD matrix are symmetric in their
indices (from `schurSet_posDef`'s Hermitian part). -/
theorem schurEntry_symm (hA : A.PosDef) (S : Finset (Fin n))
    (j k : Fin n) : schurEntry A S j k = schurEntry A S k j := by
  by_cases hj : j ∉ S <;> by_cases hk : k ∉ S
  · rw [schurEntry_eq S hj hk, schurEntry_eq S hk hj]
    have h := (schurSet_posDef hA S).isHermitian.apply
      ⟨j, Finset.mem_compl.mpr hj⟩ ⟨k, Finset.mem_compl.mpr hk⟩
    simpa using h.symm
  · simp [schurEntry, hj, hk]
  · simp [schurEntry, hj, hk]
  · simp [schurEntry, hj, hk]



/-- Diagonal survivor entries of a Schur complement of an SPD
matrix are positive (paper Section 2: `A/A_S` is again SPD). -/
theorem schurEntry_pos (hA : A.PosDef) (S : Finset (Fin n))
    {j : Fin n} (hj : j ∉ S) : 0 < schurEntry A S j j := by
  rw [schurEntry_eq S hj hj]
  exact (schurSet_posDef hA S).diag_pos



/-- Survivor Schur entries expand against the solution of the
eliminated block system (the entry form of
`A/A_S = A_RR - A_RS A_SS⁻¹ A_SR`, paper Definition 2.2). -/
theorem schurEntry_eq_sum (S : Finset (Fin n)) {j k : Fin n}
    (hj : j ∉ S) (hk : k ∉ S) :
    schurEntry A S j k = A j k - ∑ b : ↥S, A j b.1
      * ((A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val)⁻¹
        *ᵥ (fun c : ↥S => A c.1 k)) b := by
  rw [schurEntry_eq S hj hk]
  simp only [schurSet, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.submatrix_apply, Matrix.mulVec, dotProduct]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring



/-- Any solution of the eliminated block system computes the Schur
entry (the column characterization used for the quotient property). -/
theorem schurEntry_eq_of_solve (hA : A.PosDef) (T : Finset (Fin n))
    {j k : Fin n} (hj : j ∉ T) (hk : k ∉ T) (z : ↥T → ℝ)
    (hz : (A.submatrix (Subtype.val : ↥T → Fin n) Subtype.val) *ᵥ z
      = fun a : ↥T => A a.1 k) :
    schurEntry A T j k = A j k - ∑ a : ↥T, A j a.1 * z a := by
  have hT : (A.submatrix (Subtype.val : ↥T → Fin n) Subtype.val).PosDef :=
    hA.submatrix Subtype.val_injective
  let _ := hT.isUnit.invertible
  have hz2 : z = (A.submatrix (Subtype.val : ↥T → Fin n) Subtype.val)⁻¹
      *ᵥ (fun a : ↥T => A a.1 k) := by
    apply Matrix.mulVec_injective_of_isUnit hT.isUnit
    rw [hz, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
      Matrix.one_mulVec]
  rw [schurEntry_eq_sum T hj hk, hz2]



/-- The quotient property (paper Lemma 2.4, `lem:quotient`) in
entrywise form: eliminating `S` and then `v` agrees with eliminating
`S ∪ {v}` at once, via the pivot update. Bridge: the paper states an
equality of matrices on `V \ (S ∪ {v})`; here the survivor subtypes
of the two sides differ, so the equality is stated entrywise at
plain vertices. The proof exhibits the two-stage solution of the
eliminated block system (`schurEntry_eq_of_solve`). -/
theorem schur_quotient (hA : A.PosDef) (S : Finset (Fin n)) (v : Fin n)
    (hv : v ∉ S) (j k : Fin n) (hj : j ∉ insert v S)
    (hk : k ∉ insert v S) :
    schurEntry A (insert v S) j k = pivotEntry A S v j k := by
  classical
  have hjS : j ∉ S := fun h => hj (Finset.mem_insert_of_mem h)
  have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
  have hP : (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val).PosDef :=
    hA.submatrix Subtype.val_injective
  let _ := hP.isUnit.invertible
  set pfun : Fin n → Fin n → ℝ := fun x b => if h : b ∈ S then
    ((A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val)⁻¹
      *ᵥ (fun c : ↥S => A c.1 x)) ⟨b, h⟩ else 0 with hpfun
  have hSp : ∀ (a x : Fin n),
      (∑ b ∈ S, A a b * pfun x b)
        = ∑ b : ↥S, A a b.1
          * ((A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val)⁻¹
            *ᵥ (fun c : ↥S => A c.1 x)) b := by
    intro a x
    rw [← Finset.sum_coe_sort S (fun b => A a b * pfun x b)]
    apply Finset.sum_congr rfl
    intro b _
    simp [hpfun]
  have hPp : ∀ (x : Fin n), ∀ a ∈ S,
      (∑ b ∈ S, A a b * pfun x b) = A a x := by
    intro x a ha
    rw [hSp a x]
    have key : (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val)
        *ᵥ ((A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val)⁻¹
          *ᵥ (fun c : ↥S => A c.1 x)) = fun c : ↥S => A c.1 x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
        Matrix.one_mulVec]
    have hkey := congr_fun key ⟨a, ha⟩
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix] using hkey
  have hM : ∀ (a x : Fin n), a ∉ S → x ∉ S →
      schurEntry A S a x = A a x - ∑ b ∈ S, A a b * pfun x b := by
    intro a x ha hx
    rw [schurEntry_eq_sum S ha hx, hSp a x]
  have hsne : schurEntry A S v v ≠ 0 := ne_of_gt (schurEntry_pos hA S hv)
  set zv : ℝ := schurEntry A S v k / schurEntry A S v v with hzv
  have hzv_eq : zv * schurEntry A S v v = schurEntry A S v k :=
    div_mul_cancel₀ _ hsne
  set Z : Fin n → ℝ := fun a => if a = v then zv
    else if _h : a ∈ S then pfun k a - zv * pfun v a else 0 with hZ
  have hZv : Z v = zv := by simp [hZ]
  have hZS : ∀ b ∈ S, Z b = pfun k b - zv * pfun v b := by
    intro b hb
    have hbv : b ≠ v := fun h => hv (h.symm ▸ hb)
    simp [hZ, hbv, hb]
  have hrowsum : ∀ a : Fin n,
      (∑ b ∈ insert v S, A a b * Z b)
        = A a v * zv + (∑ b ∈ S, A a b * pfun k b)
          - zv * (∑ b ∈ S, A a b * pfun v b) := by
    intro a
    rw [Finset.sum_insert hv, hZv]
    have hterm : ∀ b ∈ S, A a b * Z b
        = A a b * pfun k b - zv * (A a b * pfun v b) := by
      intro b hb
      rw [hZS b hb]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    ring
  have hQz : (A.submatrix (Subtype.val : ↥(insert v S) → Fin n) Subtype.val)
      *ᵥ (fun c : ↥(insert v S) => Z c.1)
      = fun a : ↥(insert v S) => A a.1 k := by
    funext a
    have hsum : ((A.submatrix (Subtype.val : ↥(insert v S) → Fin n)
        Subtype.val) *ᵥ (fun c : ↥(insert v S) => Z c.1)) a
        = ∑ b ∈ insert v S, A a.1 b * Z b := by
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
      exact Finset.sum_coe_sort (insert v S) (fun b => A a.1 b * Z b)
    rw [hsum, hrowsum a.1]
    rcases Finset.mem_insert.mp a.2 with hav | haS
    · rw [hav]
      have e1 : (∑ b ∈ S, A v b * pfun k b)
          = A v k - schurEntry A S v k := by
        have hMvk := hM v k hv hkS; linarith
      have e2 : (∑ b ∈ S, A v b * pfun v b)
          = A v v - schurEntry A S v v := by
        have hMvv := hM v v hv hv; linarith
      rw [e1, e2]
      linarith [hzv_eq]
    · rw [hPp k a.1 haS, hPp v a.1 haS]; ring
  have hentry := schurEntry_eq_of_solve hA (insert v S) hj hk _ hQz
  rw [hentry]
  unfold pivotEntry
  have hsumj : (∑ a : ↥(insert v S), A j a.1 * Z a.1)
      = ∑ b ∈ insert v S, A j b * Z b :=
    Finset.sum_coe_sort (insert v S) (fun b => A j b * Z b)
  rw [hsumj, hrowsum j]
  have e_jk := hM j k hjS hkS
  have e_jv := hM j v hjS hv
  have hsym := schurEntry_symm hA S v k
  have e3 : zv * schurEntry A S j v
      = schurEntry A S j v * schurEntry A S k v / schurEntry A S v v := by
    rw [hzv, hsym]; ring
  linear_combination -e_jk + zv * e_jv - e3

end CholeskyCancellations

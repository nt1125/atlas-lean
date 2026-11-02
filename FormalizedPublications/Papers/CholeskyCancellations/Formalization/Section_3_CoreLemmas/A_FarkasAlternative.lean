/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Logic.Relation
import Mathlib.Analysis.LocallyConvex.Separation
import Section_2_SettingVocabularyAndConjectures.F_ConjecturesAndFeasibility

/-! # Farkas alternative (paper Section 3)

A real linear functional is a dot product; Stiemke's theorem (strict Farkas alternative), the separation input to the core lemmas. Split from `CoreLemmas.lean`.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as `Defs.lean` — entries only through `schurEntry`, levels as finsets with enumerating lists wherever the symbolic graph `G_S` is read, cancellations only through `Zeroes`/`logMag`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- A real linear functional on a finite function space is the
dot product with its values on the coordinate vectors. -/
theorem linearFunctional_apply_eq_sum {q : ℕ} (φ : (Fin q → ℝ) →ₗ[ℝ] ℝ) (x : Fin q → ℝ) :
    φ x = ∑ i, x i * φ (Pi.single i 1) := by
  classical
  have hx : x = ∑ i, Pi.single i (x i) := by
    funext i
    rw [Finset.sum_apply]
    exact (Fintype.sum_pi_single i x).symm
  conv_lhs => rw [hx]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show Pi.single i (x i) = x i • Pi.single i (1 : ℝ) by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Ne.symm h], map_smul]
  rfl



/-- `stiemke`: Stiemke's alternative (paper Section 3 roadmap,
citing Stiemke and Gordan): for a real matrix `T`, exactly one of a
strictly positive kernel vector and a separating nonnegative
combination of the rows exists. Proved by separating the kernel from
the open positive orthant (the Hahn--Banach separation theorem) and
factoring the separating functional through `T` by duality. -/
theorem stiemke {m p : ℕ} (T : Matrix (Fin m) (Fin p) ℝ) :
    ((∃ t : Fin p → ℝ, (∀ j, 0 < t j) ∧ Matrix.mulVec T t = 0)
        ∧ ¬ ∃ y : Fin m → ℝ, (∀ j, 0 ≤ Matrix.mulVec T.transpose y j)
          ∧ Matrix.mulVec T.transpose y ≠ 0)
      ∨ ((¬ ∃ t : Fin p → ℝ, (∀ j, 0 < t j) ∧ Matrix.mulVec T t = 0)
        ∧ ∃ y : Fin m → ℝ, (∀ j, 0 ≤ Matrix.mulVec T.transpose y j)
          ∧ Matrix.mulVec T.transpose y ≠ 0) := by
  classical
  have hcoord : ∀ {q : ℕ} (φ : (Fin q → ℝ) →ₗ[ℝ] ℝ) (x : Fin q → ℝ),
      φ x = ∑ i, x i * φ (Pi.single i 1) := by
    intro q φ x
    exact linearFunctional_apply_eq_sum φ x
  have hexclude : ∀ t : Fin p → ℝ, (∀ j, 0 < t j) → Matrix.mulVec T t = 0 →
      ¬ ∃ y : Fin m → ℝ, (∀ j, 0 ≤ Matrix.mulVec T.transpose y j) ∧
        Matrix.mulVec T.transpose y ≠ 0 := by
    intro t ht hTt
    rintro ⟨y, hy_nonneg, hy_ne⟩
    set z := Matrix.mulVec T.transpose y with hzdef
    have hdot_eq : dotProduct t z = 0 := by
      rw [hzdef, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hTt]
      simp [dotProduct]
    have hdot_pos : 0 < dotProduct t z := by
      rw [dotProduct]
      apply Finset.sum_pos'
      · intro i _
        exact mul_nonneg (ht i).le (hy_nonneg i)
      · obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hy_ne (funext hcon)
        exact ⟨j, Finset.mem_univ j,
          mul_pos (ht j) (lt_of_le_of_ne (hy_nonneg j) (Ne.symm hj))⟩
    linarith
  by_cases hpos : ∃ t : Fin p → ℝ, (∀ j, 0 < t j) ∧ Matrix.mulVec T t = 0
  · refine Or.inl ⟨hpos, ?_⟩
    obtain ⟨t, ht, hTt⟩ := hpos
    exact hexclude t ht hTt
  · refine Or.inr ⟨hpos, ?_⟩
    let L := T.mulVecLin
    let U : Set (Fin p → ℝ) := Set.univ.pi (fun _ => Set.Ioi 0)
    have hUmem : ∀ x : Fin p → ℝ, x ∈ U ↔ ∀ j, 0 < x j := by
      intro x
      simp [U, Set.mem_pi]
    have hUconv : Convex ℝ U := convex_pi (fun i _ => convex_Ioi 0)
    have hUopen : IsOpen U :=
      isOpen_set_pi (Set.finite_univ) (fun i _ => isOpen_Ioi)
    have hKconv : Convex ℝ (LinearMap.ker L : Set (Fin p → ℝ)) :=
      (LinearMap.ker L).convex
    have hdisj : Disjoint U (LinearMap.ker L : Set (Fin p → ℝ)) := by
      rw [Set.disjoint_left]
      intro x hxU hxK
      apply hpos
      refine ⟨x, (hUmem x).mp hxU, ?_⟩
      have hxK' : L x = 0 := by simpa using hxK
      simpa [L, Matrix.mulVecLin_apply] using hxK'
    obtain ⟨f, u, hfU, hfK⟩ :=
      geometric_hahn_banach_open hUconv hUopen hKconv hdisj
    have hfker : ∀ x ∈ LinearMap.ker L, f x = 0 := by
      intro x hx
      by_contra hne
      have hmem : ((u - 1) / f x) • x ∈ LinearMap.ker L :=
        (LinearMap.ker L).smul_mem _ hx
      have hle := hfK (((u - 1) / f x) • x) hmem
      rw [map_smul] at hle
      have hcalc : ((u - 1) / f x) • (f x) = u - 1 := by
        rw [smul_eq_mul]
        field_simp
      rw [hcalc] at hle
      linarith
    have hcoeff : ∀ j : Fin p, f (Pi.single j 1) ≤ 0 := by
      intro j
      by_contra hnot
      push Not at hnot
      set a := f (Pi.single j 1) with hadef
      set r := (|u - f 1| + 1) / a with hrdef
      have hrnum : 0 < |u - f 1| + 1 := by positivity
      have hrpos : 0 < r := div_pos hrnum hnot
      have hxU : (1 : Fin p → ℝ) + r • Pi.single j 1 ∈ U := by
        rw [hUmem]
        intro i
        by_cases h : i = j
        · subst h
          simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply,
            Pi.single_eq_same, smul_eq_mul, mul_one]
          positivity
        · simp [Pi.add_apply, Pi.smul_apply, h]
      have hlt := hfU _ hxU
      have hfx : f ((1 : Fin p → ℝ) + r • Pi.single j 1) = f 1 + r * a := by
        simp [map_add, map_smul, smul_eq_mul, hadef]
      have hra : r * a = |u - f 1| + 1 := by
        rw [hrdef]
        field_simp
      have hge : u + 1 ≤ f ((1 : Fin p → ℝ) + r • Pi.single j 1) := by
        rw [hfx, hra]
        have habs : u - f 1 ≤ |u - f 1| := le_abs_self _
        linarith
      linarith
    have hfne : f ≠ 0 := by
      intro hf0
      have h1U : (1 : Fin p → ℝ) ∈ U := by
        rw [hUmem]
        intro j
        simp
      have h1 := hfU 1 h1U
      have h0 := hfK 0 (by simp)
      simp [hf0] at h1 h0
      linarith
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual ℝ (Fin m → ℝ),
        L.dualMap ψ = -f.toLinearMap := by
      have hmem : (-f.toLinearMap) ∈ (LinearMap.ker L).dualAnnihilator := by
        rw [Submodule.mem_dualAnnihilator]
        intro x hx
        simp [hfker x hx]
      have hmem' : (-f.toLinearMap) ∈ LinearMap.range L.dualMap := by
        rwa [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
      exact hmem'
    have hz_eq : ∀ j : Fin p,
        Matrix.mulVec T.transpose (fun i => ψ (Pi.single i 1)) j
          = - f (Pi.single j 1) := by
      intro j
      have hψj : ψ (L (Pi.single j 1)) = - f (Pi.single j 1) := by
        have happ := LinearMap.congr_fun hψ (Pi.single j 1)
        simpa [LinearMap.dualMap_apply] using happ
      have hcoordψ := hcoord ψ (L (Pi.single j 1))
      have hLcoord : ∀ i, (L (Pi.single j 1)) i = T i j := by
        intro i
        simp [L, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [Matrix.mulVec, dotProduct]
      simp only [Matrix.transpose_apply]
      rw [← hψj, hcoordψ]
      apply Finset.sum_congr rfl
      intro i _
      rw [hLcoord i]
    refine ⟨fun i => ψ (Pi.single i 1), ?_, ?_⟩
    · intro j
      rw [hz_eq]
      exact neg_nonneg.mpr (hcoeff j)
    · intro hzero
      apply hfne
      apply ContinuousLinearMap.ext
      intro x
      have hcoordf := hcoord f.toLinearMap x
      have hbasis : ∀ j : Fin p, f (Pi.single j 1) = 0 := by
        intro j
        have hz0 := congrFun hzero j
        rw [hz_eq] at hz0
        simpa using hz0
      have hfzero : f.toLinearMap x = 0 := by
        rw [hcoordf]
        simp [hbasis]
      exact hfzero

end CholeskyCancellations

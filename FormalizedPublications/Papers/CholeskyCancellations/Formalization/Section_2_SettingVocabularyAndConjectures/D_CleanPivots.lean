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
import Section_2_SettingVocabularyAndConjectures.C_Chordality

/-! # Clean pivots and the Cholesky factor (paper Section 2)

Zeroes, cancellation graphs, covers, survivors, clean pivots and apexes, and the assembled Cholesky factor `factorMatrix`. Split from `Defs.lean`.
-/

open scoped Matrix

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): vertices `Fin n`, SPD = `Matrix.PosDef`, levels `Finset (Fin n)`, pivot-order list orderings, Schur entries through `schurEntry` only. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}


/-- `Zeroes A S p j k`: the pivot at `p` at level `S` zeroes the pair
`{j, k}`, by the defining equation
`(A/A_S)_{pp} (A/A_S)_{jk} = (A/A_S)_{pj} (A/A_S)_{pk}`; `p` is then
the apex of the cancellation along the route `j-p-k` (paper
Definition 2.19, `def:cancel`). -/
def Zeroes (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p j k : Fin n) : Prop :=
  p ∉ S ∧ j ∉ insert p S ∧ k ∉ insert p S ∧ j ≠ k ∧
    schurEntry A S p p * schurEntry A S j k
      = schurEntry A S p j * schurEntry A S p k



/-- `cancellationGraph A S p`: the cancellation graph `C_p(S)` (paper
Definition 2.19, `def:cancel`), on the full vertex set; `Zeroes`
keeps it supported on the survivors of `S ∪ {p}`. -/
def cancellationGraph (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p : Fin n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun j k => Zeroes A S p j k



/-- `Covers A S p q`: `C_p(S)` covers `q` (paper Definition 2.19,
`def:cancel`). -/
def Covers (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p q : Fin n) : Prop :=
  ∃ k : Fin n, Zeroes A S p q k ∨ Zeroes A S p k q



/-- `Survives A S p q`: `q` survives the pivot at `p`, i.e. is not
covered (paper Definition 2.19, `def:cancel`). No survivor
hypothesis on `q` is included: the paper's `C_p(S)` contains
only pairs of survivors of `S ∪ {p}`, so for `q ∈ S ∪ {p}` no
pair of `C_p(S)` contains `q` and survival is vacuous, exactly
as `¬ Covers` says. -/
def Survives (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p q : Fin n) : Prop :=
  ¬ Covers A S p q



/-- Survival is vacuous for the pivot itself (paper
Definition 2.19): the pivot is not a survivor of `S ∪ {p}`, so
no pair of `C_p(S)` contains it. Regression test for the
definition: an earlier version additionally required
`q ∉ insert p S`, which made this false. -/
example (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p : Fin n) : Survives A S p p := by
  rintro ⟨k, hz | hz⟩
  · exact absurd hz.2.1 (by simp)
  · exact absurd hz.2.2.1 (by simp)



/-- `IsCleanPivotAt A l S p`: `p` is a clean pivot at level `S`
(enumerated by `l`): it destroys no predicted-nonzero pair (paper
Definition 2.19, `def:cancel`). The `Enumerates l S` conjunct is
load-bearing: the paper's `G_S` depends only on the level `S`,
and `gameGraph (patternGraph A) l` is `G_S` (between survivors)
only when `l` enumerates `S`; without it the same `(S, p)`
could get different verdicts for `l = []` versus an `l`
enumerating `S`. -/
def IsCleanPivotAt (A : Matrix (Fin n) (Fin n) ℝ) (l : List (Fin n))
    (S : Finset (Fin n)) (p : Fin n) : Prop :=
  Enumerates l S ∧ ∀ j k : Fin n, Zeroes A S p j k →
    ¬ (gameGraph (patternGraph A) l).Adj j k



/-- A clean pivot at level `S` comes with an enumeration of `S`. -/
example (A : Matrix (Fin n) (Fin n) ℝ) (l : List (Fin n))
    (S : Finset (Fin n)) (p : Fin n) (h : IsCleanPivotAt A l S p) :
    Enumerates l S :=
  h.1



/-- `IsCleanApexFor A S p T`: `p` is a clean apex for the triangle
`T`: `C_p(S)` contains no pair of `T` (paper Definition 2.19,
`def:cancel`). -/
def IsCleanApexFor (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p : Fin n) (T : Finset (Fin n)) : Prop :=
  ∀ j ∈ T, ∀ k ∈ T, ¬ Zeroes A S p j k



/-- `IsCleanApex A S p`: `C_p(S)` is empty (paper Definition 2.19,
`def:cancel`, the unqualified "clean apex"). -/
def IsCleanApex (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (p : Fin n) : Prop :=
  ∀ j k : Fin n, ¬ Zeroes A S p j k



/-- `IsUniversalAt A S v`: `v` is universal in `A/A_S` — every other
survivor entry in its row is nonzero (paper Definition 2.21,
`def:universal`). -/
def IsUniversalAt (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (v : Fin n) : Prop :=
  v ∉ S ∧ ∀ j : Fin n, j ∉ S → j ≠ v → schurEntry A S v j ≠ 0



/-- `prefixListBefore σ p`: the vertices pivoted before `p` in `σ`
(paper Definition 2.23's `S_{j-1}` for `p = v_j`). -/
def prefixListBefore (σ : List (Fin n)) (p : Fin n) : List (Fin n) :=
  σ.takeWhile fun x => x ≠ p



/-- `factorEntry A σ p k`: the Cholesky factor entry `L_{kp}` by its
value `(A/A_{S})_{kp} / √(A/A_{S})_{pp}` at the level `S` preceding
`p` in `σ` (paper Definition 2.23, `def:Llink`). The assembled
matrix is `factorMatrix` below, proved to be the Cholesky factor
of `A` for the ordering `σ`: `factorMatrix_mul_transpose`,
`factorMatrix_eq_zero_of_afterIn`, `factorMatrix_diag`. -/
noncomputable def factorEntry (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : List (Fin n)) (p k : Fin n) : ℝ :=
  schurEntry A (prefixListBefore σ p).toFinset k p
    / Real.sqrt (schurEntry A (prefixListBefore σ p).toFinset p p)



/-- A vertex does not precede itself in an ordering list. -/
theorem not_mem_prefixListBefore_self (σ : List (Fin n)) (p : Fin n) :
    p ∉ prefixListBefore σ p := by
  have h2 : ∀ l : List (Fin n),
      ∀ y ∈ l.takeWhile (fun x => decide (x ≠ p)), y ≠ p := by
    intro l
    induction l with
    | nil => intro y hy; simp at hy
    | cons a l ih =>
        intro y hy
        rw [List.takeWhile_cons] at hy
        split_ifs at hy with ha
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact of_decide_eq_true ha
          · exact ih y hy
        · simp at hy
  intro h
  exact h2 σ p h rfl



/-- A factor entry is nonzero exactly when the committed Schur
entry is (the scaling denominator is a positive square root). -/
theorem factorEntry_ne_zero_iff (hA : A.PosDef) (σ : List (Fin n))
    (p k : Fin n) :
    factorEntry A σ p k ≠ 0 ↔
      schurEntry A (prefixListBefore σ p).toFinset k p ≠ 0 := by
  have hp : p ∉ (prefixListBefore σ p).toFinset := by
    rw [List.mem_toFinset]
    exact not_mem_prefixListBefore_self σ p
  have hpos : 0 < schurEntry A (prefixListBefore σ p).toFinset p p :=
    schurEntry_pos hA _ hp
  unfold factorEntry
  constructor
  · intro h
    by_contra hz
    rw [hz] at h
    simp at h
  · intro h
    exact div_ne_zero h (Real.sqrt_ne_zero'.mpr hpos)



/-- If `j` precedes `k` in `σ`, the committing prefix of the pair
is the prefix before `j`. -/
theorem prefixList_eq_prefixListBefore_cons_of_afterIn
    (σ : List (Fin n)) (hσ : IsOrdering σ) {j k : Fin n}
    (hafter : AfterIn σ j k) :
    prefixList σ j k = prefixListBefore σ j := by
  obtain ⟨l₁, l₂, l₃, hσeq⟩ := hafter
  have hσeq2 : σ = (l₁ ++ [j]) ++ (l₂ ++ k :: l₃) := by
    rw [hσeq]; simp [List.append_assoc]
  have hnd : ((l₁ ++ [j]) ++ (l₂ ++ k :: l₃)).Nodup := hσeq2 ▸ hσ.1
  have hnd1 : (l₁ ++ [j]).Nodup := (List.nodup_append.mp hnd).1
  have hj_l₁ : j ∉ l₁ := by
    intro hj
    exact (List.nodup_append.mp hnd1).2.2 j hj j
      (by simp) rfl
  have hk_l₁ : k ∉ l₁ := by
    intro hk
    exact (List.nodup_append.mp hnd).2.2 k
      (List.mem_append_left _ hk) k
      (List.mem_append_right l₂ List.mem_cons_self) rfl
  have hσeq3 : σ = l₁ ++ (j :: (l₂ ++ k :: l₃)) := by
    rw [hσeq]; simp [List.append_assoc]
  have e1 : prefixList σ j k = l₁ := by
    have hall : ∀ x ∈ l₁, decide (x ≠ j ∧ x ≠ k) = true := by
      intro x hx
      rw [decide_eq_true_eq]
      exact ⟨fun h => hj_l₁ (h ▸ hx), fun h => hk_l₁ (h ▸ hx)⟩
    rw [prefixList, hσeq3,
      takeWhile_append_of_forall hall (j :: (l₂ ++ k :: l₃)),
      List.takeWhile_cons_of_neg (by simp), List.append_nil]
  have e2 : prefixListBefore σ j = l₁ := by
    have hall : ∀ x ∈ l₁, decide (x ≠ j) = true := by
      intro x hx
      rw [decide_eq_true_eq]
      exact fun h => hj_l₁ (h ▸ hx)
    rw [prefixListBefore, hσeq3,
      takeWhile_append_of_forall hall (j :: (l₂ ++ k :: l₃)),
      List.takeWhile_cons_of_neg (by simp), List.append_nil]
  rw [e1, e2]



/-- The factor pattern is the pattern of the assembled factor
entries: for `j` preceding `k`, adjacency is exactly the committed
entry `L_{kj}` being nonzero (paper Definition 2.23, `def:Llink`). -/
theorem factorPattern_adj_iff_factorEntry (hA : A.PosDef)
    (σ : List (Fin n)) (hσ : IsOrdering σ) {j k : Fin n}
    (hafter : AfterIn σ j k) :
    (factorPattern A σ).Adj j k ↔ factorEntry A σ j k ≠ 0 := by
  have hjk : j ≠ k := by
    obtain ⟨l₁, l₂, l₃, hσeq⟩ := hafter
    have hσeq2 : σ = (l₁ ++ [j]) ++ (l₂ ++ k :: l₃) := by
      rw [hσeq]; simp [List.append_assoc]
    have hnd : ((l₁ ++ [j]) ++ (l₂ ++ k :: l₃)).Nodup :=
      hσeq2 ▸ hσ.1
    exact (List.nodup_append.mp hnd).2.2 j
      (List.mem_append_right l₁ (by simp)) k
      (List.mem_append_right l₂ List.mem_cons_self)
  have hadj : (factorPattern A σ).Adj j k ↔
      schurEntry A (prefixSet σ j k) j k ≠ 0 := by
    constructor
    · intro h
      have h2 : j ≠ k ∧ (schurEntry A (prefixSet σ j k) j k ≠ 0 ∨
          schurEntry A (prefixSet σ k j) k j ≠ 0) := by
        simpa [factorPattern, SimpleGraph.fromRel_adj] using h
      rcases h2.2 with h' | h'
      · exact h'
      · rwa [prefixSet_comm, schurEntry_symm hA] at h'
    · intro h
      simp [factorPattern, SimpleGraph.fromRel_adj, hjk, h]
  rw [hadj, factorEntry_ne_zero_iff hA, prefixSet,
    prefixList_eq_prefixListBefore_cons_of_afterIn σ hσ hafter,
    schurEntry_symm hA]



/-- Schur entries in an eliminated row or column are the junk
value `0`. -/
theorem schurEntry_eq_zero_of_mem_left {S : Finset (Fin n)}
    {j k : Fin n} (hj : j ∈ S) : schurEntry A S j k = 0 := by
  unfold schurEntry
  split_ifs with h
  · exact absurd hj (Finset.mem_compl.mp h)
  · rfl
  · rfl



/-- Telescoping the Schur update along a list of pivots: the
entry at the initial level is the sum of the squared-magnitude
update terms `L_{jp} L_{kp}` over the pivots plus the entry at the
final level. -/
theorem factorEntry_telescope (hA : A.PosDef) :
    ∀ (l₀ l t : List (Fin n)), (l₀ ++ l ++ t).Nodup →
      ∀ j k : Fin n, j ∉ l₀ → k ∉ l₀ → j ∉ l → k ∉ l →
      schurEntry A l₀.toFinset j k =
        (∑ p ∈ l.toFinset, factorEntry A (l₀ ++ l ++ t) p j
          * factorEntry A (l₀ ++ l ++ t) p k) +
          schurEntry A (l₀ ++ l).toFinset j k := by
  intro l₀ l
  induction l generalizing l₀ with
  | nil =>
      intro t _ j k _ _ _ _
      simp
  | cons p l ih =>
      intro t hnd j k hj₀ hk₀ hj hk
      have hjp : j ≠ p := by
        have h2 : ¬ (j = p ∨ j ∈ l) := by
          simpa only [List.mem_cons] using hj
        exact fun h => h2 (Or.inl h)
      have hjl : j ∉ l := by
        have h2 : ¬ (j = p ∨ j ∈ l) := by
          simpa only [List.mem_cons] using hj
        exact fun h => h2 (Or.inr h)
      have hkp : k ≠ p := by
        have h2 : ¬ (k = p ∨ k ∈ l) := by
          simpa only [List.mem_cons] using hk
        exact fun h => h2 (Or.inl h)
      have hkl : k ∉ l := by
        have h2 : ¬ (k = p ∨ k ∈ l) := by
          simpa only [List.mem_cons] using hk
        exact fun h => h2 (Or.inr h)
      have hp₀ : p ∉ l₀ := by
        intro hp
        exact (List.nodup_append.mp
          (List.nodup_append.mp hnd).1).2.2 p hp p
          List.mem_cons_self rfl
      have hpl : p ∉ l := by
        have h2 : (p :: l).Nodup :=
          (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
        exact (List.nodup_cons.mp h2).1
      have hσσ : (l₀ ++ [p]) ++ l ++ t = l₀ ++ (p :: l) ++ t := by
        simp [List.append_assoc]
      have hpre_p : prefixListBefore (l₀ ++ (p :: l) ++ t) p
          = l₀ := by
        rw [show l₀ ++ (p :: l) ++ t = l₀ ++ (p :: (l ++ t)) from by
              simp [List.append_assoc]]
        rw [prefixListBefore,
          takeWhile_append_of_forall (p := fun x => decide (x ≠ p))
            (by
              intro x hx
              rw [decide_eq_true_eq]
              exact fun h => hp₀ (h ▸ hx)) (p :: (l ++ t)),
          List.takeWhile_cons_of_neg (by simp), List.append_nil]
      have hpS : p ∉ l₀.toFinset := by
        rwa [List.mem_toFinset]
      have hjS : j ∉ insert p l₀.toFinset := by
        rw [Finset.mem_insert]
        push Not
        exact ⟨hjp, by rwa [List.mem_toFinset]⟩
      have hkS : k ∉ insert p l₀.toFinset := by
        rw [Finset.mem_insert]
        push Not
        exact ⟨hkp, by rwa [List.mem_toFinset]⟩
      have hpos : 0 < schurEntry A l₀.toFinset p p :=
        schurEntry_pos hA _ hpS
      have hstep : schurEntry A l₀.toFinset j k
          = factorEntry A (l₀ ++ (p :: l) ++ t) p j
            * factorEntry A (l₀ ++ (p :: l) ++ t) p k
            + schurEntry A (insert p l₀.toFinset) j k := by
        have hfe : ∀ x : Fin n,
            factorEntry A (l₀ ++ (p :: l) ++ t) p x
              = schurEntry A l₀.toFinset x p
                / Real.sqrt (schurEntry A l₀.toFinset p p) := by
          intro x
          unfold factorEntry
          rw [hpre_p]
        have hprod : factorEntry A (l₀ ++ (p :: l) ++ t) p j
            * factorEntry A (l₀ ++ (p :: l) ++ t) p k
            = schurEntry A l₀.toFinset j p
              * schurEntry A l₀.toFinset k p
              / schurEntry A l₀.toFinset p p := by
          rw [hfe j, hfe k, div_mul_div_comm,
            Real.mul_self_sqrt (le_of_lt hpos)]
        rw [hprod, schur_quotient hA l₀.toFinset p hpS j k hjS hkS]
        unfold pivotEntry
        ring
      have hj0p : j ∉ l₀ ++ [p] := by
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hj₀, hjp⟩
      have hk0p : k ∉ l₀ ++ [p] := by
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hk₀, hkp⟩
      have ih' := ih (l₀ ++ [p]) t (hσσ.symm ▸ hnd) j k hj0p hk0p
        hjl hkl
      rw [hσσ] at ih'
      have hS1 : (l₀ ++ [p]).toFinset = insert p l₀.toFinset := by
        ext x
        simp [Finset.mem_insert]
      have hS2 : ((l₀ ++ [p]) ++ l).toFinset
          = (l₀ ++ (p :: l)).toFinset := by
        congr 1
        simp [List.append_assoc]
      rw [hS1, hS2] at ih'
      rw [List.toFinset_cons,
        Finset.sum_insert (by rwa [List.mem_toFinset]), hstep, ih']
      ring



/-- `factorMatrix A σ`: the assembled Cholesky factor `L`, with
`(k, p)` entry the factor entry `L_{kp}` of Definition 2.23. -/
noncomputable def factorMatrix (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : List (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun k p => factorEntry A σ p k



/-- The head of the remaining `dropWhile` is one of the pair. -/
theorem dropWhile_head_mem_pair {σ : List (Fin n)} {j k e : Fin n}
    {t : List (Fin n)}
    (h : σ.dropWhile (fun x => decide (x ≠ j ∧ x ≠ k)) = e :: t) :
    e = j ∨ e = k := by
  induction σ with
  | nil => simp at h
  | cons a σ ih =>
      rw [List.dropWhile_cons] at h
      split_ifs at h with ha
      · exact ih h
      · injection h with hae _
        subst hae
        by_contra hcon
        push Not at hcon
        exact ha (by rw [decide_eq_true_eq]; exact hcon)



/-- The assembled factor satisfies `L Lᵀ = A`. This is the bridge
from the paper's Definition 2.23 entry formula to an actual
matrix factorization; together with `σ`-order lower triangularity
(`factorMatrix_eq_zero_of_afterIn`) and the positive diagonal
(`factorMatrix_diag`) it identifies `factorMatrix A σ` as the
Cholesky factor for `σ`, and with
`factorPattern_adj_iff_factorEntry` it says the factor pattern is
the pattern of this factor. -/
theorem factorMatrix_mul_transpose (hA : A.PosDef)
    (σ : List (Fin n)) (hσ : IsOrdering σ) :
    factorMatrix A σ * (factorMatrix A σ)ᵀ = A := by
  have hσmem : ∀ x : Fin n, x ∈ σ := by
    intro x
    have h1 : σ.toFinset = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [List.toFinset_card_of_nodup hσ.1, hσ.2, Fintype.card_fin]
    exact List.mem_toFinset.mp (by rw [h1]; exact Finset.mem_univ x)
  ext j k
  set S : Finset (Fin n) := (prefixList σ j k).toFinset with hSdef
  obtain ⟨e, t, hd⟩ : ∃ e t, σ.dropWhile
      (fun x => decide (x ≠ j ∧ x ≠ k)) = e :: t := by
    have hne : σ.dropWhile
        (fun x => decide (x ≠ j ∧ x ≠ k)) ≠ [] := by
      intro hnil
      have hsplit := List.takeWhile_append_dropWhile
        (p := fun x => decide (x ≠ j ∧ x ≠ k)) (l := σ)
      rw [hnil, List.append_nil] at hsplit
      have hjmem : j ∈ prefixList σ j k := by
        have h2 : j ∈ σ.takeWhile
            (fun x => decide (x ≠ j ∧ x ≠ k)) := by
          rw [hsplit]
          exact hσmem j
        exact h2
      exact (mem_prefixList_imp hjmem).1 rfl
    exact List.exists_cons_of_ne_nil hne
  have he : e = j ∨ e = k := dropWhile_head_mem_pair hd
  have hsplit0 : σ = prefixList σ j k ++ e :: t := by
    have h2 := List.takeWhile_append_dropWhile
      (p := fun x => decide (x ≠ j ∧ x ≠ k)) (l := σ)
    rw [hd] at h2
    exact h2.symm
  have hsplit : σ = (prefixList σ j k ++ [e]) ++ t := by
    calc σ = prefixList σ j k ++ e :: t := hsplit0
      _ = (prefixList σ j k ++ [e]) ++ t := by
          simp [List.append_assoc]
  have hjpre : j ∉ prefixList σ j k :=
    fun hj => (mem_prefixList_imp hj).1 rfl
  have hkpre : k ∉ prefixList σ j k :=
    fun hk => (mem_prefixList_imp hk).2 rfl
  have hepre : e ∉ prefixList σ j k := by
    intro h
    have hnd : ((prefixList σ j k ++ [e]) ++ t).Nodup :=
      hsplit ▸ hσ.1
    exact (List.nodup_append.mp
      (List.nodup_append.mp hnd).1).2.2 e h e (by simp) rfl
  have hpre_e : prefixListBefore σ e = prefixList σ j k := by
    have h3 : (prefixList σ j k ++ [e]) ++ t
        = prefixList σ j k ++ (e :: t) := by
      simp [List.append_assoc]
    rw [prefixListBefore]
    conv_lhs => rw [hsplit, h3]
    rw [takeWhile_append_of_forall (p := fun x => decide (x ≠ e))
        (by
          intro x hx
          rw [decide_eq_true_eq]
          exact fun h => hepre (h ▸ hx)) (e :: t),
      List.takeWhile_cons_of_neg (by simp), List.append_nil]
  have heS : e ∉ S := by
    rw [hSdef, List.mem_toFinset]
    exact hepre
  have hpos : 0 < schurEntry A S e e := schurEntry_pos hA S heS
  have htele := factorEntry_telescope hA [] (prefixList σ j k)
    (e :: t) (by
      have h2 : [] ++ prefixList σ j k ++ (e :: t) = σ := by
        rw [List.nil_append]
        exact hsplit0.symm
      exact h2.symm ▸ hσ.1) j k (by simp) (by simp) hjpre hkpre
  simp only [List.nil_append, List.toFinset_nil, schurEntry_empty]
    at htele
  rw [← hsplit0, ← hSdef] at htele
  have hfin : schurEntry A S j k
      = factorEntry A σ e j * factorEntry A σ e k := by
    have hfe : ∀ x : Fin n, factorEntry A σ e x
        = schurEntry A S x e / Real.sqrt (schurEntry A S e e) := by
      intro x
      unfold factorEntry
      rw [hpre_e, ← hSdef]
    rw [hfe j, hfe k, div_mul_div_comm,
      Real.mul_self_sqrt (le_of_lt hpos)]
    rcases he with hej | hek
    · rw [← hej, mul_div_cancel_left₀ _ (ne_of_gt hpos)]
      exact schurEntry_symm hA _ e k
    · rw [← hek, mul_div_cancel_right₀ _ (ne_of_gt hpos)]
  rw [hfin] at htele
  have hvan : ∀ p ∈ (Finset.univ : Finset (Fin n)),
      p ∉ insert e S →
      factorEntry A σ p j * factorEntry A σ p k = 0 := by
    intro p _ hp
    rw [Finset.mem_insert, hSdef, List.mem_toFinset] at hp
    push Not at hp
    obtain ⟨hpe, hppre⟩ := hp
    have hpt : p ∈ t := by
      have h2 : p ∈ (prefixList σ j k ++ [e]) ++ t :=
        hsplit ▸ hσmem p
      rcases List.mem_append.mp h2 with h | h
      · rcases List.mem_append.mp h with h | h
        · exact absurd h hppre
        · simp only [List.mem_singleton] at h
          exact absurd h hpe
      · exact h
    have hein : e ∈ prefixListBefore σ p := by
      have h3 : (prefixList σ j k ++ [e]) ++ t
          = prefixList σ j k ++ (e :: t) := by
        simp [List.append_assoc]
      rw [prefixListBefore, hsplit, h3,
        takeWhile_append_of_forall (p := fun x => decide (x ≠ p))
          (by
            intro x hx
            rw [decide_eq_true_eq]
            have hnd : ((prefixList σ j k ++ [e]) ++ t).Nodup :=
              hsplit ▸ hσ.1
            exact fun h => (List.nodup_append.mp hnd).2.2 x
              (List.mem_append_left [e] hx) p hpt h) (e :: t)]
      apply List.mem_append_right
      rw [List.takeWhile_cons_of_pos (by
        simp only [decide_eq_true_eq]
        exact fun h => hpe h.symm)]
      exact List.mem_cons_self
    have hfe0 : factorEntry A σ p e = 0 := by
      unfold factorEntry
      rw [schurEntry_eq_zero_of_mem_left (by
        rwa [List.mem_toFinset])]
      exact zero_div _
    rcases he with rfl | rfl
    · simp [hfe0]
    · simp [hfe0]
  have hsum : ∑ p : Fin n, factorEntry A σ p j
      * factorEntry A σ p k = A j k := by
    rw [← Finset.sum_subset (Finset.subset_univ _) hvan,
      Finset.sum_insert heS,
      htele]
    ring
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, factorMatrix]
  exact hsum



/-- If `k` precedes `p` in `σ`, then `k` is in the prefix before
`p`. -/
theorem mem_prefixListBefore_of_afterIn {σ : List (Fin n)}
    (hσ : IsOrdering σ) {k p : Fin n} (h : AfterIn σ k p) :
    k ∈ prefixListBefore σ p := by
  obtain ⟨l₁, l₂, l₃, hσeq⟩ := h
  have hσeq2 : σ = (l₁ ++ k :: l₂) ++ p :: l₃ := by
    rw [hσeq]
  have hnd : ((l₁ ++ k :: l₂) ++ p :: l₃).Nodup := hσeq2 ▸ hσ.1
  have hp : ∀ x ∈ l₁ ++ k :: l₂, x ≠ p := by
    intro x hx hxp
    exact (List.nodup_append.mp hnd).2.2 x hx p List.mem_cons_self hxp
  have hall : ∀ x ∈ l₁ ++ k :: l₂, decide (x ≠ p) = true := by
    intro x hx
    rw [decide_eq_true_eq]
    exact hp x hx
  have e : prefixListBefore σ p = l₁ ++ k :: l₂ := by
    rw [prefixListBefore, hσeq2,
      takeWhile_append_of_forall hall (p :: l₃),
      List.takeWhile_cons_of_neg (by simp), List.append_nil]
  rw [e]
  exact List.mem_append_right l₁ List.mem_cons_self



/-- `factorMatrix` is lower triangular in `σ`-order: the `(k, p)`
entry vanishes when the row index `k` is pivoted before the column
index `p`. The numerator is a Schur entry in an eliminated row,
hence the junk zero of `schurEntry_eq_zero_of_mem_left`. Together
with `factorMatrix_mul_transpose` and `factorMatrix_diag` this
pins `factorMatrix A σ` down as the Cholesky factor of `A` for the
ordering `σ` — `L Lᵀ = A` alone would also hold for `L Q` with
orthogonal `Q`. -/
theorem factorMatrix_eq_zero_of_afterIn {σ : List (Fin n)}
    (hσ : IsOrdering σ) {k p : Fin n} (h : AfterIn σ k p) :
    factorMatrix A σ k p = 0 := by
  have hkS : k ∈ (prefixListBefore σ p).toFinset :=
    List.mem_toFinset.mpr (mem_prefixListBefore_of_afterIn hσ h)
  unfold factorMatrix factorEntry
  rw [schurEntry_eq_zero_of_mem_left hkS, zero_div]



/-- The diagonal entries of `factorMatrix` are positive square
roots of the pivots. -/
theorem factorMatrix_diag (hA : A.PosDef) (σ : List (Fin n))
    (p : Fin n) :
    factorMatrix A σ p p
      = Real.sqrt (schurEntry A (prefixListBefore σ p).toFinset p p) ∧
    0 < factorMatrix A σ p p := by
  have hp : p ∉ (prefixListBefore σ p).toFinset := by
    rw [List.mem_toFinset]
    exact not_mem_prefixListBefore_self σ p
  have hpos : 0 < schurEntry A (prefixListBefore σ p).toFinset p p :=
    schurEntry_pos hA _ hp
  have heq : factorMatrix A σ p p
      = Real.sqrt (schurEntry A (prefixListBefore σ p).toFinset p p) := by
    unfold factorMatrix factorEntry
    rw [Real.div_sqrt]
  exact ⟨heq, heq.symm ▸ Real.sqrt_pos.mpr hpos⟩

end CholeskyCancellations

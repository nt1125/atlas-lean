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
import Section_2_SettingVocabularyAndConjectures.E_StrategyVocabulary

/-! # Conjectures and feasibility (paper Section 2)

The two conjectures (`first_schur_conjecture`, `fill_graph_conjecture`), slots and feasibility (`IsFeasibleAt`), realizability, partial correlations, and log-magnitudes.
-/

open scoped Matrix

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): vertices `Fin n`, SPD = `Matrix.PosDef`, levels `Finset (Fin n)`, pivot-order list orderings, Schur entries through `schurEntry` only. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}


/-- `FirstSchurClean A σ`: the first Schur complement along `σ` has
no cancellation at a predicted-nonzero position (paper
Conjecture 2.26's requirement, `conj:2`). Positions of the first
Schur complement are pairs of survivors, so `j` and `k` are
restricted away from the first pivot `p`. -/
def FirstSchurClean (A : Matrix (Fin n) (Fin n) ℝ) (σ : List (Fin n)) :
    Prop :=
  ∀ (p : Fin n) (l : List (Fin n)), σ = p :: l →
    ∀ j k : Fin n, j ≠ p → k ≠ p →
      (gameGraph (patternGraph A) [p]).Adj j k →
        schurEntry A {p} j k ≠ 0



/-- `first_schur_conjecture`: every irreducible SPD matrix admits an
ordering whose first Schur complement has no cancellation at a
predicted-nonzero position (paper Conjecture 2.26, `conj:2` —
"Conjecture 2" of Section 1.3; refuted at order 4 in the paper). -/
def first_schur_conjecture : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ),
    A.PosDef → IsIrreducible A →
      ∃ σ : List (Fin n), IsOrdering σ ∧ FirstSchurClean A σ



/-- `fill_graph_conjecture`: every irreducible SPD matrix admits a
clean ordering (paper Conjecture 2.27, `conj:1` — "Conjecture 1" of
Section 1.3; refuted at every even order at least 6 in the paper). -/
def fill_graph_conjecture : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ),
    A.PosDef → IsIrreducible A →
      ∃ σ : List (Fin n), IsOrdering σ ∧ IsCleanOrdering A σ



/-- A slot `(S, j, k)`: the formal demand `(A/A_S)_{jk} = 0` (paper
Definition 2.28, `def:slots`). -/
structure Slot (n : ℕ) where
  /-- The level of the slot (paper Definition 2.28). -/
  level : Finset (Fin n)
  /-- The first index of the demanded zero (paper Definition 2.28). -/
  fst : Fin n
  /-- The second index of the demanded zero (paper Definition 2.28). -/
  snd : Fin n
  /-- The first index survives the level (paper Definition 2.28). -/
  hf : fst ∉ level
  /-- The second index survives the level (paper Definition 2.28). -/
  hs : snd ∉ level
  /-- The two indices are distinct (paper Definition 2.28). -/
  hne : fst ≠ snd



/-- `Slot.Active A s`: the slot's demanded zero holds in `A` (paper
Definition 2.28, `def:slots`). -/
def Slot.Active (A : Matrix (Fin n) (Fin n) ℝ) (s : Slot n) : Prop :=
  schurEntry A s.level s.fst s.snd = 0



/-- `Slot.Spoils s A σ`: the slot spoils `σ` — its level is exactly
the committing prefix of its pair, which is predicted nonzero there
(paper Definition 2.29, `def:blocking`; prediction is read in the
paper's symbolic graph of `A`'s pattern). -/
def Slot.Spoils (s : Slot n) (A : Matrix (Fin n) (Fin n) ℝ)
    (σ : List (Fin n)) : Prop :=
  s.level = prefixSet σ s.fst s.snd ∧
    (gameGraph (patternGraph A) (prefixList σ s.fst s.snd)).Adj
      s.fst s.snd



/-- `IsBlocking H G`: every ordering is spoiled by some slot of `H`,
for matrices of pattern `G` (paper Definition 2.29, `def:blocking`;
spoiling is evaluated against a chosen realization, whose pattern is
all that enters). -/
def IsBlocking (H : Set (Slot n)) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ A : Matrix (Fin n) (Fin n) ℝ, patternGraph A = G →
    ∀ σ : List (Fin n), IsOrdering σ → ∃ s ∈ H, s.Spoils A σ



/-- `IsRealizable H G`: some SPD matrix of pattern `G` makes every
slot of `H` active (paper Definition 2.29, `def:blocking`). -/
def IsRealizable (H : Set (Slot n)) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) ℝ,
    A.PosDef ∧ patternGraph A = G ∧ ∀ s ∈ H, s.Active A



/-- `partialCorr A S j k`: the partial correlation
`(A/A_S)_{jk} / √((A/A_S)_{jj} (A/A_S)_{kk})` (paper
Definition 2.32, `def:t`). Junk `0`-dividing values off the survivors
follow `schurEntry`. -/
noncomputable def partialCorr (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (j k : Fin n) : ℝ :=
  schurEntry A S j k
    / Real.sqrt (schurEntry A S j j * schurEntry A S k k)



/-- `logMag A S j k`: the log-magnitude `t⁽ˢ⁾_{jk} = -log |r⁽ˢ⁾_{jk}|`
(paper Definition 2.32, `def:t`). Totalisation: the paper puts
`t = +∞` at a zero entry, but `ℝ` has no `+∞`, so here `t` is
real-valued and totalised — at a zero entry
`partialCorr = 0`, `Real.log 0 = 0` in Lean, and `logMag = 0`,
not `+∞`. Every statement using `logMag` guards this away by
assuming the entries in play are nonzero (see `logMag_pos` and
`cancellation_additive`), where the two conventions agree and
`t > 0`; no lemma relies on the totalised value `0` at a zero
entry. An `Option`/`ENNReal` encoding would track `+∞`
faithfully but would complicate every arithmetic use, so the
totalisation is documented here instead. -/
noncomputable def logMag (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (j k : Fin n) : ℝ :=
  - Real.log |partialCorr A S j k|



/-- Partial correlations at a level have absolute value below `1`
off the diagonal (paper Definition 2.32's `-1 < r < 1` for
`j ≠ k`, from the `2×2` minor of `A/A_S`). -/
theorem abs_partialCorr_lt_one (hA : A.PosDef) (S : Finset (Fin n))
    {j k : Fin n} (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    |partialCorr A S j k| < 1 := by
  have hne : (⟨j, Finset.mem_compl.mpr hj⟩ : Survivors S)
      ≠ ⟨k, Finset.mem_compl.mpr hk⟩ := by simp [hjk]
  have hm := posDef_two_mul_sub_pos (schurSet_posDef hA S) hne
  rw [← schurEntry_eq S hj hj, ← schurEntry_eq S hk hk,
    ← schurEntry_eq S hj hk, ← schurEntry_eq S hk hj] at hm
  rw [schurEntry_symm hA S k j] at hm
  have hdj := schurEntry_pos hA S hj
  have hdk := schurEntry_pos hA S hk
  have hsq : (schurEntry A S j k) ^ 2
      < schurEntry A S j j * schurEntry A S k k := by nlinarith
  unfold partialCorr
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [div_lt_one (Real.sqrt_pos.mpr (mul_pos hdj hdk))]
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) hsq



/-- Log-magnitudes at nonzero survivor entries are positive (paper
Definition 2.32's range `t ∈ (0, ∞)` at nonzero entries). -/
theorem logMag_pos (hA : A.PosDef) (S : Finset (Fin n))
    {j k : Fin n} (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k)
    (hne : schurEntry A S j k ≠ 0) : 0 < logMag A S j k := by
  unfold logMag
  have hlt := abs_partialCorr_lt_one hA S hj hk hjk
  have hpos : 0 < |partialCorr A S j k| := by
    apply abs_pos.mpr
    unfold partialCorr
    exact div_ne_zero hne
      (Real.sqrt_ne_zero'.mpr
        (mul_pos (schurEntry_pos hA S hj) (schurEntry_pos hA S hk)))
  have hlog := Real.log_neg hpos hlt
  linarith



/-- Log-magnitudes are symmetric in their indices for SPD matrices
(paper Definition 2.32: `t` lives on unordered pairs). -/
theorem logMag_symm (hA : A.PosDef) (S : Finset (Fin n))
    (j k : Fin n) : logMag A S j k = logMag A S k j := by
  unfold logMag partialCorr
  rw [schurEntry_symm hA S j k, schurEntry_symm hA S j j,
    schurEntry_symm hA S k k, mul_comm]



/-- `IsFeasibleAt H S`: the additive system imposed by the slots of
`H` at the single level `S` has a strictly positive solution (paper
Definition 2.29, `def:blocking`). Each slot beyond `S` reading
`(S ∪ {v}, j, k)` imposes `t_{jk} = t_{vj} + t_{vk}` by the additive
lemma; here feasibility is stated directly for those equations. The
solution `t` is symmetric, as the paper's `t⁽ˢ⁾` is a function on
unordered pairs.

Formal-system caveat (paper Lemma 2.33, `lem:additive`): this
definition is matrix-free, so each slot imposes its equation
unconditionally, as a formal equation. The paper's lemma supplies
that equation from a realizing matrix only when both legs
`(A/A_S)_{vj}`, `(A/A_S)_{vk}` are nonzero — a hypothesis this
definition cannot state, having no matrix. Hence
`¬ IsFeasibleAt H S` (formal infeasibility) does not by itself
refute realizability: dropping the equations of zero-leg slots
could leave a feasible system. The correct bridge is
`feasible_of_active_of_legs_ne` below: active slots with
nonzero legs do imply feasibility, with `t` the log-magnitudes
of `A/A_S`. In particular the `¬ IsFeasibleAt` conclusions of
`general_cycle` and `four_cycle_infeasible` are formal-system
infeasibility, and no result in the development uses them to
conclude `¬ IsRealizable`. The Pairing Lemma's use of
`IsFeasibleAt` is likewise about the formal system, matching
the paper's "a slot imposes the relation" reading there. -/
def IsFeasibleAt (H : Set (Slot n)) (S : Finset (Fin n)) : Prop :=
  ∃ t : Fin n → Fin n → ℝ,
    (∀ j k : Fin n, 0 < t j k) ∧ (∀ j k : Fin n, t j k = t k j) ∧
    ∀ s ∈ H, ∃ v : Fin n, s.level = insert v S ∧ v ∉ S ∧
      t s.fst s.snd = t v s.fst + t v s.snd



/-- Cancellation is additive in `t` (paper Lemma 2.33,
`lem:additive`): with nonzero legs, `(A/A_{S∪{v}})_{jk} = 0` iff
`r⁽ˢ⁾_{jk} = r⁽ˢ⁾_{vj} r⁽ˢ⁾_{vk}`, and then
`t⁽ˢ⁾_{jk} = t⁽ˢ⁾_{vj} + t⁽ˢ⁾_{vk}`; conversely, the additive relation plus
agreement of signs gives the cancellation. Signs are read as a
positive product (both sides nonzero under the hypotheses). -/
theorem cancellation_additive (hA : A.PosDef) (S : Finset (Fin n))
    (v j k : Fin n) (hv : v ∉ S) (hj : j ∉ insert v S)
    (hk : k ∉ insert v S) (hlegj : schurEntry A S v j ≠ 0)
    (hlegk : schurEntry A S v k ≠ 0) :
    (schurEntry A (insert v S) j k = 0 ↔
      partialCorr A S j k
        = partialCorr A S v j * partialCorr A S v k) ∧
    (schurEntry A (insert v S) j k = 0 →
      logMag A S j k = logMag A S v j + logMag A S v k) ∧
    (logMag A S j k = logMag A S v j + logMag A S v k →
      0 < partialCorr A S j k
          * (partialCorr A S v j * partialCorr A S v k) →
        schurEntry A (insert v S) j k = 0) := by
  have hjS : j ∉ S := fun h => hj (Finset.mem_insert_of_mem h)
  have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
  have hdv : 0 < schurEntry A S v v := schurEntry_pos hA S hv
  have hdj : 0 < schurEntry A S j j := schurEntry_pos hA S hjS
  have hdk : 0 < schurEntry A S k k := schurEntry_pos hA S hkS
  have hsqrt : Real.sqrt (schurEntry A S v v * schurEntry A S j j)
      * Real.sqrt (schurEntry A S v v * schurEntry A S k k)
      = schurEntry A S v v
        * Real.sqrt (schurEntry A S j j * schurEntry A S k k) := by
    rw [← Real.sqrt_mul (mul_nonneg hdv.le hdj.le)]
    have harg : schurEntry A S v v * schurEntry A S j j
        * (schurEntry A S v v * schurEntry A S k k)
        = schurEntry A S v v ^ 2
          * (schurEntry A S j j * schurEntry A S k k) := by ring
    rw [harg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hdv.le]
  have hprod : partialCorr A S v j * partialCorr A S v k
      = (schurEntry A S j v * schurEntry A S k v / schurEntry A S v v)
        / Real.sqrt (schurEntry A S j j * schurEntry A S k k) := by
    unfold partialCorr
    rw [schurEntry_symm hA S v j, schurEntry_symm hA S v k]
    field_simp
    linear_combination (-(schurEntry A S j v * schurEntry A S k v)) * hsqrt
  have hiff0 : schurEntry A (insert v S) j k = 0 ↔
      schurEntry A S j k
        = schurEntry A S j v * schurEntry A S k v
          / schurEntry A S v v := by
    rw [schur_quotient hA S v hv j k hj hk]
    simp [pivotEntry, sub_eq_zero]
  have hsqrtne : Real.sqrt (schurEntry A S j j * schurEntry A S k k) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos hdj hdk)
  have hreq : partialCorr A S j k
        = partialCorr A S v j * partialCorr A S v k ↔
      schurEntry A S j k
        = schurEntry A S j v * schurEntry A S k v
          / schurEntry A S v v := by
    rw [hprod]
    unfold partialCorr
    exact (div_eq_div_iff hsqrtne hsqrtne).trans (mul_left_inj' hsqrtne)
  have hpart1 : schurEntry A (insert v S) j k = 0 ↔
      partialCorr A S j k
        = partialCorr A S v j * partialCorr A S v k := by
    rw [hreq]; exact hiff0
  have hr1 : partialCorr A S v j ≠ 0 := by
    unfold partialCorr
    exact div_ne_zero hlegj
      (Real.sqrt_ne_zero'.mpr (mul_pos hdv hdj))
  have hr2 : partialCorr A S v k ≠ 0 := by
    unfold partialCorr
    exact div_ne_zero hlegk
      (Real.sqrt_ne_zero'.mpr (mul_pos hdv hdk))
  refine ⟨hpart1, ?_, ?_⟩
  · intro h0
    have hr := hpart1.mp h0
    unfold logMag
    have habs : |partialCorr A S j k|
        = |partialCorr A S v j| * |partialCorr A S v k| := by
      rw [hr, abs_mul]
    rw [habs, Real.log_mul (abs_pos.mpr hr1).ne' (abs_pos.mpr hr2).ne']
    ring
  · intro ht hsign
    apply hpart1.mpr
    have habs : |partialCorr A S j k|
        = |partialCorr A S v j| * |partialCorr A S v k| := by
      have hr0 : partialCorr A S j k ≠ 0 := by
        intro hz
        rw [hz, zero_mul] at hsign
        exact lt_irrefl 0 hsign
      have h1 : Real.log |partialCorr A S j k|
          = Real.log (|partialCorr A S v j| * |partialCorr A S v k|) := by
        have h2 := ht
        unfold logMag at h2
        rw [Real.log_mul (abs_pos.mpr hr1).ne' (abs_pos.mpr hr2).ne']
        linarith
      have h2 := congrArg Real.exp h1
      rwa [Real.exp_log (abs_pos.mpr hr0),
        Real.exp_log (mul_pos (abs_pos.mpr hr1) (abs_pos.mpr hr2))] at h2
    have habs2 : |partialCorr A S j k|
        = |partialCorr A S v j * partialCorr A S v k| := by
      rw [habs, abs_mul]
    rcases abs_eq_abs.mp habs2 with h | h
    · exact h
    · exfalso
      have hle : partialCorr A S j k
          * (partialCorr A S v j * partialCorr A S v k) ≤ 0 := by
        rw [h]
        calc -(partialCorr A S v j * partialCorr A S v k)
              * (partialCorr A S v j * partialCorr A S v k)
            = -((partialCorr A S v j * partialCorr A S v k) ^ 2) := by ring
          _ ≤ 0 := neg_nonpos.mpr (sq_nonneg _)
      linarith



/-- Soundness of the formal feasibility system: slots active for a
matrix `A` at levels one above `S`, with both legs nonzero in
`A/A_S`, imply `IsFeasibleAt H S` (paper Definition 2.29's
"realizable implies feasible", in the exact form Lemma 2.33
supports). The leg hypotheses are essential: without them a
realizing matrix need not satisfy the formal equations. The
witness `t` is `logMag A S` at survivor pairs with distinct
indices and a nonzero entry, and `1` elsewhere (so `t > 0`
everywhere, including the diagonal and eliminated indices, where
the formal `t` has no paper counterpart). -/
theorem feasible_of_active_of_legs_ne (hA : A.PosDef)
    (S : Finset (Fin n)) (H : Set (Slot n))
    (hlevel : ∀ s ∈ H, ∃ v : Fin n, s.level = insert v S ∧ v ∉ S)
    (hact : ∀ s ∈ H, s.Active A)
    (hlegs : ∀ s ∈ H, ∀ v : Fin n, s.level = insert v S → v ∉ S →
      schurEntry A S v s.fst ≠ 0 ∧ schurEntry A S v s.snd ≠ 0) :
    IsFeasibleAt H S := by
  classical
  refine ⟨fun j k =>
    if j ∉ S ∧ k ∉ S ∧ j ≠ k ∧ schurEntry A S j k ≠ 0 then
      logMag A S j k else 1, ?_, ?_, ?_⟩
  · intro j k
    dsimp only
    by_cases hc : j ∉ S ∧ k ∉ S ∧ j ≠ k ∧ schurEntry A S j k ≠ 0
    · rw [ite_eq_left hc]
      exact logMag_pos hA S hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    · rw [ite_eq_right hc]
      exact one_pos
  · intro j k
    dsimp only
    by_cases hc : j ∉ S ∧ k ∉ S ∧ j ≠ k ∧ schurEntry A S j k ≠ 0
    · have hc' : k ∉ S ∧ j ∉ S ∧ k ≠ j ∧ schurEntry A S k j ≠ 0 := by
        obtain ⟨hj, hk, hjk, hne⟩ := hc
        refine ⟨hk, hj, Ne.symm hjk, ?_⟩
        rw [schurEntry_symm hA S k j]
        exact hne
      rw [ite_eq_left hc, ite_eq_left hc']
      exact logMag_symm hA S j k
    · have hc' :
          ¬ (k ∉ S ∧ j ∉ S ∧ k ≠ j ∧ schurEntry A S k j ≠ 0) := by
        intro h
        apply hc
        obtain ⟨hk, hj, hkj, hne⟩ := h
        refine ⟨hj, hk, Ne.symm hkj, ?_⟩
        rw [schurEntry_symm hA S j k]
        exact hne
      rw [ite_eq_right hc, ite_eq_right hc']
  · intro s hs
    obtain ⟨v, hlevelv, hvS⟩ := hlevel s hs
    obtain ⟨hlegj, hlegk⟩ := hlegs s hs v hlevelv hvS
    have hfS : s.fst ∉ S := fun h => by
      apply s.hf
      rw [hlevelv]
      exact Finset.mem_insert_of_mem h
    have hsS : s.snd ∉ S := fun h => by
      apply s.hs
      rw [hlevelv]
      exact Finset.mem_insert_of_mem h
    have hfj : s.fst ∉ insert v S := by
      rw [← hlevelv]
      exact s.hf
    have hsj : s.snd ∉ insert v S := by
      rw [← hlevelv]
      exact s.hs
    have h0 : schurEntry A (insert v S) s.fst s.snd = 0 := by
      rw [← hlevelv]
      exact hact s hs
    have hpart := (cancellation_additive hA S v s.fst s.snd hvS hfj hsj
      hlegj hlegk).1.mp h0
    have hlegj' : partialCorr A S v s.fst ≠ 0 := by
      unfold partialCorr
      exact div_ne_zero hlegj (Real.sqrt_ne_zero'.mpr (mul_pos
        (schurEntry_pos hA S hvS) (schurEntry_pos hA S hfS)))
    have hlegk' : partialCorr A S v s.snd ≠ 0 := by
      unfold partialCorr
      exact div_ne_zero hlegk (Real.sqrt_ne_zero'.mpr (mul_pos
        (schurEntry_pos hA S hvS) (schurEntry_pos hA S hsS)))
    have hne : schurEntry A S s.fst s.snd ≠ 0 := by
      have h3 : partialCorr A S s.fst s.snd ≠ 0 := by
        rw [hpart]
        exact mul_ne_zero hlegj' hlegk'
      unfold partialCorr at h3
      exact (div_ne_zero_iff.mp h3).1
    refine ⟨v, hlevelv, hvS, ?_⟩
    dsimp only
    have hadd := (cancellation_additive hA S v s.fst s.snd hvS hfj hsj
      hlegj hlegk).2.1 h0
    have c1 : s.fst ∉ S ∧ s.snd ∉ S ∧ s.fst ≠ s.snd ∧
        schurEntry A S s.fst s.snd ≠ 0 :=
      ⟨hfS, hsS, s.hne, hne⟩
    have hvf : v ≠ s.fst := by
      intro hh
      subst hh
      exact hfj (Finset.mem_insert_self _ _)
    have hvs : v ≠ s.snd := by
      intro hh
      subst hh
      exact hsj (Finset.mem_insert_self _ _)
    have c2 : v ∉ S ∧ s.fst ∉ S ∧ v ≠ s.fst ∧
        schurEntry A S v s.fst ≠ 0 :=
      ⟨hvS, hfS, hvf, hlegj⟩
    have c3 : v ∉ S ∧ s.snd ∉ S ∧ v ≠ s.snd ∧
        schurEntry A S v s.snd ≠ 0 :=
      ⟨hvS, hsS, hvs, hlegk⟩
    rw [ite_eq_left c1, ite_eq_left c2, ite_eq_left c3]
    exact hadd

end CholeskyCancellations

/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Logic.Relation
import Mathlib.Analysis.LocallyConvex.Separation
import Section_3_CoreLemmas.C_ExchangeLemma

/-! # Universal pivots and refill (paper Section 3)

The log-magnitude maximum edge, universal pivots, refill, and the dense-safety / universal-successor steps. Split from `CoreLemmas.lean`.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as `Defs.lean` — entries only through `schurEntry`, levels as finsets with enumerating lists wherever the symbolic graph `G_S` is read, cancellations only through `Zeroes`/`logMag`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- At a dense level, a log-magnitude-maximizing pair is not
covered (the shared argument of paper Lemmas 3.3 and 3.6: an
additive relation would produce a strictly larger `t`-value). -/
theorem not_covers_of_logMag_max (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) {S : Finset (Fin n)} {p q : Fin n}
    (hp : p ∉ S) (hq : q ∉ S) (hpq : p ≠ q)
    (hdense : ∀ j : Fin n, j ∉ S → ∀ k : Fin n, k ∉ S → j ≠ k →
      schurEntry A S j k ≠ 0)
    (hmax : ∀ j : Fin n, j ∉ S → ∀ k : Fin n, k ∉ S → j ≠ k →
      logMag A S j k ≤ logMag A S p q) :
    ¬ Covers A S p q := by
  rintro ⟨k, hz | hz⟩
  · have hkS : k ∉ S := fun h => hz.2.2.1 (Finset.mem_insert_of_mem h)
    have hzero : schurEntry A (insert p S) q k = 0 :=
      (zeroes_iff_entry_eq_zero A hA hp hz.2.1 hz.2.2.1 hz.2.2.2.1).mp hz
    have hadd := (cancellation_additive hA S p q k hp hz.2.1 hz.2.2.1
      (hdense p hp q hq hpq) (hdense p hp k hkS (fun h => by
        have hmem := hz.2.2.1
        simp [h] at hmem))).2.1 hzero
    have hpos : 0 < logMag A S p k :=
      logMag_pos hA S hp hkS (fun h => by
        have hmem := hz.2.2.1
        simp [h] at hmem) (hdense p hp k hkS (fun h => by
        have hmem := hz.2.2.1
        simp [h] at hmem))
    have hle := hmax q (fun h => hz.2.1 (Finset.mem_insert_of_mem h)) k hkS
      hz.2.2.2.1
    linarith
  · have hkS : k ∉ S := fun h => hz.2.1 (Finset.mem_insert_of_mem h)
    have hzero : schurEntry A (insert p S) k q = 0 :=
      (zeroes_iff_entry_eq_zero A hA hp hz.2.1 hz.2.2.1 hz.2.2.2.1).mp hz
    have hpk : p ≠ k := fun h => by
      have hmem := hz.2.1
      simp [h] at hmem
    have hadd := (cancellation_additive hA S p k q hp hz.2.1 hz.2.2.1
      (hdense p hp k hkS hpk) (hdense p hp q hq hpq)).2.1 hzero
    have hpos : 0 < logMag A S p k :=
      logMag_pos hA S hp hkS hpk (hdense p hp k hkS hpk)
    have hle := hmax k hkS q hq hz.2.2.2.1
    linarith



/-- The Max-Edge Lemma (paper Lemma 3.3, `lem:maxedge`): for a
log-magnitude-maximizing pair `(p, q)`, no pair of `C_p` contains
`q`, so `q` survives `p`. -/
theorem max_edge (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hdense : ∀ i j : Fin n, i ≠ j → A i j ≠ 0)
    (p q : Fin n) (hpq : p ≠ q)
    (hmax : ∀ i j : Fin n, i ≠ j → logMag A ∅ i j ≤ logMag A ∅ p q) :
    ¬ Covers A ∅ p q ∧ Survives A ∅ p q := by
  have hdense' : ∀ j : Fin n, j ∉ (∅ : Finset (Fin n)) →
      ∀ k : Fin n, k ∉ (∅ : Finset (Fin n)) → j ≠ k →
      schurEntry A ∅ j k ≠ 0 := by
    intro j _ k _ hjk
    rw [schurEntry_empty]
    exact hdense j k hjk
  have hmax' : ∀ j : Fin n, j ∉ (∅ : Finset (Fin n)) →
      ∀ k : Fin n, k ∉ (∅ : Finset (Fin n)) → j ≠ k →
      logMag A ∅ j k ≤ logMag A ∅ p q :=
    fun j _ k _ hjk => hmax j k hjk
  have hnc := not_covers_of_logMag_max (p := p) (q := q) A hA
    (by simp) (by simp) hpq hdense' hmax'
  refine ⟨hnc, ?_⟩
  exact hnc



/-- The Zero-leg equivalence (paper Lemma 3.4, `lem:zeroleg`): a
zero leg makes the pivot update the identity on its pair, and the
two slots across the pivot agree. -/
theorem zero_leg (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (S : Finset (Fin n)) (j k v : Fin n)
    (hj : j ∉ S) (hk : k ∉ S) (hv : v ∉ S) (_hjk : j ≠ k)
    (hjv : j ≠ v) (hkv : k ≠ v) (hleg : schurEntry A S j v = 0) :
    schurEntry A (insert v S) j k = schurEntry A S j k ∧
      (schurEntry A S j k = 0 ↔ schurEntry A (insert v S) j k = 0) := by
  have hjI : j ∉ insert v S := by simp [hjv, hj]
  have hkI : k ∉ insert v S := by simp [hkv, hk]
  have h1 : schurEntry A (insert v S) j k = schurEntry A S j k := by
    rw [schur_quotient hA S v hv j k hjI hkI]
    simp [pivotEntry, hleg]
  exact ⟨h1, by rw [h1]⟩



/-- Fact 1 (paper Lemma 3.5, `lem:fact1`): a universal pivot
destroys every pre-existing zero, and the zeros after it are exactly
`C_v(S)`. -/
theorem universal_pivot_refill (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (S : Finset (Fin n)) (v : Fin n)
    (huniv : IsUniversalAt A S v) :
    (∀ j k : Fin n, j ∉ insert v S → k ∉ insert v S → j ≠ k →
        schurEntry A S j k = 0 →
          schurEntry A (insert v S) j k
            = - (schurEntry A S j v * schurEntry A S k v
                / schurEntry A S v v)
              ∧ schurEntry A (insert v S) j k ≠ 0)
      ∧ ∀ j k : Fin n, j ∉ insert v S → k ∉ insert v S → j ≠ k →
          (schurEntry A (insert v S) j k = 0 ↔ Zeroes A S v j k) := by
  constructor
  · intro j k hj hk _hjk h0
    have hd : schurEntry A S v v ≠ 0 :=
      ne_of_gt (schurEntry_pos hA S huniv.1)
    have hlegj : schurEntry A S j v ≠ 0 := by
      have hjS : j ∉ S := fun h => hj (Finset.mem_insert_of_mem h)
      have hjv : j ≠ v :=
        fun h => hj (by rw [h]; exact Finset.mem_insert_self v S)
      rw [schurEntry_symm hA S j v]
      exact huniv.2 j hjS hjv
    have hlegk : schurEntry A S k v ≠ 0 := by
      have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
      have hkv : k ≠ v :=
        fun h => hk (by rw [h]; exact Finset.mem_insert_self v S)
      rw [schurEntry_symm hA S k v]
      exact huniv.2 k hkS hkv
    have hval : schurEntry A (insert v S) j k
        = - (schurEntry A S j v * schurEntry A S k v
            / schurEntry A S v v) := by
      rw [schur_quotient hA S v huniv.1 j k hj hk]
      simp [pivotEntry, h0]
    refine ⟨hval, ?_⟩
    rw [hval]
    exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hlegj hlegk) hd)
  · intro j k hj hk hjk
    exact (zeroes_iff_entry_eq_zero A hA huniv.1 hj hk hjk).symm



/-- Dense Safety (paper Lemma 3.6, `lem:dense`): when every
survivor pair is nonzero, `C_p(S)` does not cover the partner `q` of
a maximizing pair. -/
theorem dense_safety (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (S : Finset (Fin n))
    (hdense : ∀ j k : Fin n, j ∉ S → k ∉ S → j ≠ k →
      schurEntry A S j k ≠ 0)
    (p q : Fin n) (hp : p ∉ S) (hq : q ∉ S) (hpq : p ≠ q)
    (hmax : ∀ j k : Fin n, j ∉ S → k ∉ S → j ≠ k →
      logMag A S j k ≤ logMag A S p q) :
    ¬ Covers A S p q :=
  not_covers_of_logMag_max A hA hp hq hpq
    (fun j hj k hk hjk => hdense j k hj hk hjk)
    (fun j hj k hk hjk => hmax j k hj hk hjk)



/-- The Universal Successor lemma
(paper Lemma 3.8, `lem:univsucc`): the weakest neighbour of a
universal pivot is universal after the pivot. -/
theorem universal_successor (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (S : Finset (Fin n)) (p q : Fin n) (huniv : IsUniversalAt A S p)
    (hq : q ∉ S) (hqp : q ≠ p)
    (hweak : ∀ x : Fin n, x ∉ S → schurEntry A S q x ≠ 0 →
      logMag A S q x ≤ logMag A S p q) :
    IsUniversalAt A (insert p S) q := by
  refine ⟨by simp [hq, hqp], ?_⟩
  intro k hk hqk
  have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
  have hkp : k ≠ p :=
    fun h => hk (by rw [h]; exact Finset.mem_insert_self p S)
  have hpq_leg : schurEntry A S p q ≠ 0 := huniv.2 q hq hqp
  have hpk_leg : schurEntry A S p k ≠ 0 := huniv.2 k hkS hkp
  by_cases hqk0 : schurEntry A S q k = 0
  · have hqI : q ∉ insert p S := by simp [hqp, hq]
    exact (universal_pivot_refill A hA S p huniv).1 q k hqI hk
      (Ne.symm hqk) hqk0 |>.2
  · by_contra hzero
    have hqI : q ∉ insert p S := by simp [hqp, hq]
    have hadd := (cancellation_additive hA S p q k huniv.1 hqI hk
      hpq_leg hpk_leg).2.1 hzero
    have hpos : 0 < logMag A S p k :=
      logMag_pos hA S huniv.1 hkS (Ne.symm hkp) hpk_leg
    have hle := hweak k hkS hqk0
    linarith



/-- `refill`: the Refill Lemma (paper Lemma 3.9, `lem:refill`):
under `ω(G_A) ≤ 3`, if `u` cancels the shared edge of two triangles
then the other apex restores it. Proved: a `u`-`w` edge would make a
`4`-clique; the zero-leg mover then preserves the `j`-`w` and `k`-`w`
legs, and the quotient rule at `w` computes the restored value. -/
theorem refill {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (homega : (patternGraph A).cliqueNum ≤ 3)
    (j k u w : Fin n)
    (hjk : j ≠ k) (huj : u ≠ j) (huk : u ≠ k)
    (hwj : w ≠ j) (hwk : w ≠ k) (hwu : w ≠ u)
    (hjkA : (patternGraph A).Adj j k) (hjuA : (patternGraph A).Adj j u)
    (hkuA : (patternGraph A).Adj k u) (hjwA : (patternGraph A).Adj j w)
    (hkwA : (patternGraph A).Adj k w) (hz : Zeroes A ∅ u j k) :
    A u w = 0 ∧ schurEntry A {u} j w = A j w ∧
      schurEntry A {u} j w ≠ 0 ∧
      schurEntry A {u} k w = A k w ∧
      schurEntry A {u} k w ≠ 0 ∧
      schurEntry A (insert w {u}) j k
        = - (A j w * A k w / schurEntry A {u} w w) ∧
      schurEntry A (insert w {u}) j k ≠ 0 := by
  have hentry : ∀ x y : Fin n, (patternGraph A).Adj x y → A x y ≠ 0 := by
    intro x y hxy
    have hadj : x ≠ y ∧ (A x y ≠ 0 ∨ A y x ≠ 0) := by
      simpa [patternGraph, SimpleGraph.fromRel_adj] using hxy
    rcases hadj.2 with h | h
    · exact h
    · rwa [posDef_apply_comm hA] at h
  have huw : A u w = 0 := by
    by_contra hne
    have hclique : (patternGraph A).IsClique (({j, k, u, w} : Finset (Fin n)) : Set (Fin n)) := by
      intro x hx y hy hxy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx hy
      have hadj_uw : (patternGraph A).Adj u w := by
        simp [patternGraph, SimpleGraph.fromRel_adj, show u ≠ w from Ne.symm hwu, hne]
      have s1 := hjkA.symm; have s2 := hjuA.symm; have s3 := hjwA.symm
      have s4 := hkuA.symm; have s5 := hkwA.symm; have s6 := hadj_uw.symm
      rcases hx with rfl | rfl | rfl | rfl <;>
        rcases hy with rfl | rfl | rfl | rfl <;>
        first | contradiction | assumption
    have hcard : ({j, k, u, w} : Finset (Fin n)).card = 4 := by
      classical
      rw [Finset.card_insert_of_notMem (by simp [hjk, Ne.symm huj, Ne.symm hwj]),
        Finset.card_insert_of_notMem (by simp [Ne.symm huk, Ne.symm hwk]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hwu]),
        Finset.card_singleton]
    have hle := hclique.card_le_cliqueNum
    rw [hcard] at hle
    omega
  have hwu0 : schurEntry A ∅ w u = 0 := by
    rw [schurEntry_empty, posDef_apply_comm hA, huw]
  have hMjw : schurEntry A {u} j w = A j w := by
    have h1 : schurEntry A (insert u ∅) w j = schurEntry A ∅ w j :=
      (zero_leg A hA ∅ w j u (by simp) (by simp) (by simp)
        hwj hwu (Ne.symm huj) hwu0).1
    have h2 : schurEntry A (insert u ∅) j w = A j w := by
      rw [schurEntry_symm hA, h1, schurEntry_empty,
        posDef_apply_comm hA]
    simpa using h2
  have hMkw : schurEntry A {u} k w = A k w := by
    have h1 : schurEntry A (insert u ∅) w k = schurEntry A ∅ w k :=
      (zero_leg A hA ∅ w k u (by simp) (by simp) (by simp)
        hwk hwu (Ne.symm huk) hwu0).1
    have h2 : schurEntry A (insert u ∅) k w = A k w := by
      rw [schurEntry_symm hA, h1, schurEntry_empty,
        posDef_apply_comm hA]
    simpa using h2
  have hMjk : schurEntry A {u} j k = 0 := by
    have := (zeroes_iff_entry_eq_zero A hA (p := u) (j := j) (k := k)
      (by simp) (Finset.notMem_singleton.mpr (Ne.symm huj))
      (Finset.notMem_singleton.mpr (Ne.symm huk)) hjk).mp hz
    simpa using this
  have hfin : schurEntry A (insert w {u}) j k
      = - (A j w * A k w / schurEntry A {u} w w) := by
    rw [schur_quotient hA {u} w (Finset.notMem_singleton.mpr hwu) j k
      (by simp [Ne.symm hwj, Ne.symm huj]) (by simp [Ne.symm hwk, Ne.symm huk])]
    simp [pivotEntry, hMjw, hMkw, hMjk]
  have hjw0 : A j w ≠ 0 := hentry j w hjwA
  have hkw0 : A k w ≠ 0 := hentry k w hkwA
  have hww : schurEntry A {u} w w ≠ 0 :=
    ne_of_gt (schurEntry_pos hA {u}
      (Finset.notMem_singleton.mpr hwu))
  refine ⟨huw, hMjw, ?_, hMkw, ?_, hfin, ?_⟩
  · rw [hMjw]; exact hjw0
  · rw [hMkw]; exact hkw0
  · rw [hfin]
    exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hjw0 hkw0) hww)

end CholeskyCancellations

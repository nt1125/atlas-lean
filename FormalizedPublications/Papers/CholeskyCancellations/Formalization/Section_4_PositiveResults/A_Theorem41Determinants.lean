/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.TakeWhile
import Section_3_CoreLemmas.F_CyclesAndMonotone

/-! # Theorem 4.1: almost-principal determinants (paper Section 4)

Almost-principal minors, the Jones–West-style determinant formula, and the forest theorem (`forest_clean`): every ordering of a forest pattern is clean.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as the Section 2 files; graph classes are predicates on `SimpleGraph (Fin n)` patterns and cleanliness is quantified per SPD realization through `PatternAdmitsPerMatrixCleanOrdering`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- The almost-principal submatrix on rows `S ∪ {j}`, columns
`S ∪ {k}`, indexed by `Option ↥S` with `none` for `j`/`k`. This is
the numerator matrix in the Jones–West determinant formula behind
the forest theorem (paper Theorem 4.1 proof). -/
noncomputable def almostPrincipal (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (j k : Fin n) :
    Matrix (Option ↥S) (Option ↥S) ℝ :=
  fun r c => A (match r with | none => j | some s => s.val)
    (match c with | none => k | some s => s.val)



/-- Reindexing equivalence `Option ↥S ≃ ↥S ⊕ Unit`. -/
def optionSumEquiv (S : Finset (Fin n)) : Option ↥S ≃ ↥S ⊕ Unit where
  toFun := fun o => match o with
    | none => Sum.inr ()
    | some s => Sum.inl s
  invFun := fun s => match s with
    | Sum.inl s => some s
    | Sum.inr _ => none
  left_inv := fun o => by cases o <;> rfl
  right_inv := fun s => by cases s <;> rfl



/-- The almost-principal-minor identity:
`det A_{S∪{j}, S∪{k}} = det A_{S,S} · (A/A_S)_{jk}` (the first
display in the proof of paper Theorem 4.1). -/
theorem almostPrincipal_det {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (S : Finset (Fin n)) {j k : Fin n}
    (hj : j ∉ S) (hk : k ∉ S) :
    (almostPrincipal A S j k).det
      = (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val).det
        * schurEntry A S j k := by
  have hT : (A.submatrix (Subtype.val : ↥S → Fin n)
      Subtype.val).PosDef :=
    hA.submatrix Subtype.val_injective
  let _ := hT.isUnit.invertible
  have hblocks : (almostPrincipal A S j k).reindex
        (optionSumEquiv S) (optionSumEquiv S)
      = Matrix.fromBlocks
          (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val)
          (Matrix.of (fun (s : ↥S) (_ : Unit) => A s.val k))
          (Matrix.of (fun (_ : Unit) (s : ↥S) => A j s.val))
          (Matrix.of (fun (_ _ : Unit) => A j k)) := by
    ext (r c)
    cases r <;> cases c <;>
      simp [almostPrincipal, Matrix.reindex, Matrix.fromBlocks,
        optionSumEquiv, Matrix.submatrix]
  calc (almostPrincipal A S j k).det
      = ((almostPrincipal A S j k).reindex (optionSumEquiv S)
          (optionSumEquiv S)).det :=
        (Matrix.det_reindex_self (optionSumEquiv S)
          (almostPrincipal A S j k)).symm
    _ = (Matrix.fromBlocks
          (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val)
          (Matrix.of (fun (s : ↥S) (_ : Unit) => A s.val k))
          (Matrix.of (fun (_ : Unit) (s : ↥S) => A j s.val))
          (Matrix.of (fun (_ _ : Unit) => A j k))).det := by
        rw [hblocks]
    _ = (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val).det
          * ((Matrix.of (fun (_ _ : Unit) => A j k))
            - Matrix.of (fun (_ : Unit) (s : ↥S) => A j s.val)
              * ⅟((A.submatrix (Subtype.val : ↥S → Fin n)
                  (Subtype.val : ↥S → Fin n)) : Matrix ↥S ↥S ℝ)
              * Matrix.of (fun (s : ↥S) (_ : Unit) => A s.val k)).det :=
        Matrix.det_fromBlocks₁₁ _ _ _ _
    _ = (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val).det
          * schurEntry A S j k := by
        congr 1
        rw [Matrix.det_unique, schurEntry_eq_sum S hj hk,
          Matrix.invOf_eq_nonsing_inv]
        simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.mulVec,
          dotProduct, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro i _
        ring



/-- Cofactor expansion of a determinant over `Option α` along the
`none` column: the `none` term times the complementary principal
minor, minus the `some w` terms times the minors that move the
`none` row into the `w` slot. Used for the induction behind the
Jones–West path formula for forests (paper Theorem 4.1). -/
theorem det_option_col_expansion {α : Type*} [DecidableEq α] [Fintype α]
    (M : Matrix (Option α) (Option α) ℝ) :
    M.det = M none none * (M.submatrix some some).det
      - ∑ w : α, M (some w) none
          * (Matrix.of (fun u t => M (if u = w then none else some u) (some t))).det := by
  have hσ : ∀ (c : Option α) (τ : Equiv.Perm α),
      Equiv.Perm.decomposeOption.symm (c, τ) = Equiv.swap none c * τ.optionCongr :=
    fun c τ => rfl
  have happ : ∀ (c : Option α) (τ : Equiv.Perm α) (i : Option α),
      Equiv.Perm.decomposeOption.symm (c, τ) i
        = Equiv.swap none c (Option.map τ i) := by
    intro c τ i
    rw [hσ]
    simp [Equiv.Perm.mul_apply, Equiv.optionCongr]
  have hfiber_none : (∑ τ : Equiv.Perm α,
        ((Equiv.Perm.sign (Equiv.Perm.decomposeOption.symm (none, τ)) : ℤ) : ℝ)
          * ∏ i, M (Equiv.Perm.decomposeOption.symm (none, τ) i) i)
      = M none none * (M.submatrix some some).det := by
    rw [Matrix.det_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    have hsign : Equiv.Perm.sign (Equiv.Perm.decomposeOption.symm (none, τ))
        = Equiv.Perm.sign τ := by
      rw [hσ]
      simp [Equiv.Perm.sign_mul, Equiv.optionCongr_sign]
    have hprod : ∏ i, M (Equiv.Perm.decomposeOption.symm (none, τ) i) i
        = M none none * ∏ a, M (some (τ a)) (some a) := by
      rw [Fintype.prod_option]
      congr 1
    rw [hsign, hprod]
    simp only [Matrix.submatrix_apply]
    ring
  have hfiber_some : ∀ w : α, (∑ τ : Equiv.Perm α,
        ((Equiv.Perm.sign (Equiv.Perm.decomposeOption.symm (some w, τ)) : ℤ) : ℝ)
          * ∏ i, M (Equiv.Perm.decomposeOption.symm (some w, τ) i) i)
      = - M (some w) none
          * (Matrix.of (fun u t => M (if u = w then none else some u) (some t))).det := by
    intro w
    rw [Matrix.det_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    have hsign : ((Equiv.Perm.sign (Equiv.Perm.decomposeOption.symm (some w, τ)) : ℤ) : ℝ)
        = - ((Equiv.Perm.sign τ : ℤ) : ℝ) := by
      rw [hσ, Equiv.Perm.sign_mul, Equiv.optionCongr_sign,
        Equiv.Perm.sign_swap (by simp : (none : Option α) ≠ some w)]
      simp
    have hprod : ∏ i, M (Equiv.Perm.decomposeOption.symm (some w, τ) i) i
        = M (some w) none * ∏ a, (Matrix.of
            (fun u t => M (if u = w then none else some u) (some t))) (τ a) a := by
      rw [Fintype.prod_option]
      congr 1
      refine Finset.prod_congr rfl (fun a _ => ?_)
      rw [happ]
      simp only [Option.map_some, Matrix.of_apply]
      split_ifs with hτ
      · rw [hτ]; simp
      · exact congrArg (fun x => M x (some a))
          (Equiv.swap_apply_of_ne_of_ne (by simp) (by simp [hτ]))
    rw [hsign, hprod]
    ring
  rw [Matrix.det_apply',
    ← Equiv.sum_comp Equiv.Perm.decomposeOption.symm
      (fun σ => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M (σ i) i),
    Fintype.sum_prod_type, Fintype.sum_option, hfiber_none]
  rw [Finset.sum_congr rfl (fun w _ => hfiber_some w), sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun w _ => by ring)




/-- Equivalence between `↥S` and `Option ↥(S \ {w})` sending `w` to `none`. -/
def sdiffOneEquiv (S : Finset (Fin n)) (w : Fin n) (hw : w ∈ S) :
    ↥S ≃ Option ↥(S \ {w}) where
  toFun := fun s => if h : s = ⟨w, hw⟩ then none
    else some ⟨s.val, Finset.mem_sdiff.mpr ⟨s.2,
      by simp only [Finset.notMem_singleton]; exact fun hh => h (Subtype.ext hh)⟩⟩
  invFun := fun o => match o with
    | none => ⟨w, hw⟩
    | some t => ⟨t.val, (Finset.mem_sdiff.mp t.2).1⟩
  left_inv := by
    intro s
    by_cases hs : s = ⟨w, hw⟩ <;> simp [hs]
  right_inv := by
    intro o
    cases o with
    | none => simp
    | some t =>
        have hne : (⟨t.val, (Finset.mem_sdiff.mp t.2).1⟩ : ↥S) ≠ ⟨w, hw⟩ := by
          simp only [ne_eq, Subtype.mk.injEq]
          exact fun hh => by
            have h2 := (Finset.mem_sdiff.mp t.2).2
            simp [hh] at h2
        simp [hne]



theorem almostPrincipal_minor_det (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (j k w : Fin n) (hw : w ∈ S) :
    (Matrix.of (fun u t : ↥S => almostPrincipal A S j k
        (if u = ⟨w, hw⟩ then none else some u) (some t))).det
      = (almostPrincipal A (S \ {w}) j w).det := by
  classical
  have h : (Matrix.of (fun u t : ↥S => almostPrincipal A S j k
        (if u = ⟨w, hw⟩ then none else some u) (some t)))
      = (almostPrincipal A (S \ {w}) j w).reindex (sdiffOneEquiv S w hw).symm
          (sdiffOneEquiv S w hw).symm := by
    ext u t
    by_cases hu : u = ⟨w, hw⟩ <;> by_cases ht : t = ⟨w, hw⟩ <;>
      simp [hu, ht, Matrix.reindex, Matrix.submatrix, almostPrincipal,
        sdiffOneEquiv]
  rw [h, Matrix.det_reindex_self]



theorem almostPrincipal_det_expansion (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (j k : Fin n) :
    (almostPrincipal A S j k).det
      = A j k * (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val).det
        - ∑ w : ↥S, A w.val k
            * (almostPrincipal A (S \ {w.val}) j w.val).det := by
  classical
  have h1 : (almostPrincipal A S j k) none none = A j k := rfl
  have h2 : ((almostPrincipal A S j k).submatrix some some).det
      = (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val).det := by
    congr 1
  have h3 : ∀ w : ↥S, (almostPrincipal A S j k) (some w) none
        * (Matrix.of (fun u t => almostPrincipal A S j k
            (if u = w then none else some u) (some t))).det
      = A w.val k * (almostPrincipal A (S \ {w.val}) j w.val).det := fun w =>
    congrArg₂ _ rfl (almostPrincipal_minor_det A S j k w.val w.2)
  rw [det_option_col_expansion, h1, h2,
    Finset.sum_congr rfl (fun w _ => h3 w)]



/-- Adjacency in the pattern graph of an SPD matrix is a nonzero
entry (in the given orientation, by symmetry). -/
theorem patternGraph_adj_entry {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {x y : Fin n}
    (h : (patternGraph A).Adj x y) : A x y ≠ 0 := by
  have h' : x ≠ y ∧ (A x y ≠ 0 ∨ A y x ≠ 0) := by
    simpa [patternGraph, SimpleGraph.fromRel_adj] using h
  rcases h'.2 with hh | hh
  · exact hh
  · rwa [posDef_apply_comm hA] at hh



/-- A nonzero entry between distinct vertices is adjacency in the
pattern graph. -/
theorem patternGraph_adj_of_entry {A : Matrix (Fin n) (Fin n) ℝ} {x y : Fin n} (hxy : x ≠ y)
    (h : A x y ≠ 0) : (patternGraph A).Adj x y := by
  simp [patternGraph, SimpleGraph.fromRel_adj, hxy, h]



/-- Vanishing criterion: if every `j`–`k` path passes through a vertex
`x` outside `S ∪ {j, k}`, the level-`S` Schur entry is zero. -/
theorem schurEntry_eq_zero_of_forall_path {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef)
    (S : Finset (Fin n)) {j k x : Fin n} (hj : j ∉ S) (hk : k ∉ S)
    (hjk : j ≠ k) (hxj : x ≠ j) (hxk : x ≠ k) (hxS : x ∉ S)
    (hpath : ∀ p : (patternGraph A).Path j k, x ∈ (p : (patternGraph A).Walk j k).support) :
    schurEntry A S j k = 0 := by
  by_contra hne
  have hgame : (gameGraph (patternGraph A) S.toList).Adj j k :=
    numeric_le_gameGraph hA S.toList j k (by
      rw [Finset.toList_toFinset]
      exact numericPattern_adj_mk S j k hjk hne)
  have henum : Enumerates S.toList S :=
    ⟨Finset.nodup_toList S, Finset.toList_toFinset S⟩
  obtain ⟨W, hW⟩ := (level_graph_path S.toList S henum j k hj hk hjk).mp hgame
  have hxmem : x ∈ W.support :=
    SimpleGraph.Walk.support_toPath_subset_support W (hpath W.toPath)
  rcases hW x hxmem with h | h | h
  · exact hxj h
  · exact hxk h
  · exact hxS h




/-- A walk between distinct vertices has a first step. -/
theorem exists_cons_of_ne {G : SimpleGraph (Fin n)} {j k : Fin n}
    (hjk : j ≠ k) (W : G.Walk j k) :
    ∃ v, ∃ h : G.Adj j v, ∃ W' : G.Walk v k, W = SimpleGraph.Walk.cons h W' := by
  cases W with
  | nil => exact absurd rfl hjk
  | cons h W' => exact ⟨_, h, W', rfl⟩



/-- The almost-principal minor is nonzero when a path through the
level joins the pair: the inductive heart of the Jones–West path
formula for forests. Induction on the level size, expanding the
determinant along the `k` column (`almostPrincipal_det_expansion`);
in a forest exactly one term survives. -/
theorem almostPrincipal_det_ne_zero {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hF : (patternGraph A).IsAcyclic) :
    ∀ (m : ℕ) (S : Finset (Fin n)), S.card ≤ m → ∀ j k : Fin n,
      j ∉ S → k ∉ S → j ≠ k → HasPathThrough (patternGraph A) S j k →
      (almostPrincipal A S j k).det ≠ 0 := by
  intro m
  induction m with
  | zero =>
      intro S hS j k hj hk hjk hpath
      have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
      subst hS0
      obtain ⟨W, hW⟩ := hpath
      obtain ⟨v, h, W', hWW⟩ := exists_cons_of_ne hjk W
      have hv : v ∈ W.support := by
        rw [hWW, SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ W'.start_mem_support
      have hadj : (patternGraph A).Adj j k := by
        rcases hW v hv with hh | hh | hh
        · exact absurd hh.symm h.ne
        · subst hh; exact h
        · simp at hh
      have hdet : (almostPrincipal A ∅ j k).det = A j k := by
        rw [Matrix.det_unique]
        rfl
      rw [hdet]
      exact patternGraph_adj_entry hA hadj
  | succ m ih =>
      intro S hS j k hj hk hjk hpath
      classical
      obtain ⟨W, hW⟩ := hpath
      set P := W.toPath with hPdef
      have hPsub : ∀ x ∈ (P : (patternGraph A).Walk j k).support,
          x = j ∨ x = k ∨ x ∈ S :=
        fun x hx => hW x (SimpleGraph.Walk.support_toPath_subset_support W hx)
      set Q := P.reverse with hQdef
      have hQsupp : (Q : (patternGraph A).Walk k j).support
          = (P : (patternGraph A).Walk j k).support.reverse :=
        SimpleGraph.Walk.support_reverse _
      obtain ⟨vr, hadjQ, w', hQcons⟩ :=
        exists_cons_of_ne (Ne.symm hjk) (Q : (patternGraph A).Walk k j)
      have hQsupp2 : (Q : (patternGraph A).Walk k j).support
          = k :: w'.support := by
        rw [hQcons, SimpleGraph.Walk.support_cons]
      have hknodup : k ∉ w'.support := by
        have hnd := Q.2.support_nodup
        rw [hQsupp2] at hnd
        exact (List.nodup_cons.mp hnd).1
      have hvrP : vr ∈ (P : (patternGraph A).Walk j k).support := by
        have h1 : vr ∈ (Q : (patternGraph A).Walk k j).support := by
          rw [hQsupp2]
          exact List.mem_cons_of_mem _ w'.start_mem_support
        rw [hQsupp] at h1
        exact List.mem_reverse.mp h1
      have hvrk : vr ≠ k := hadjQ.ne.symm
      have hbranch : ∀ w : ↥S, w.val ≠ vr →
          A w.val k * (almostPrincipal A (S \ {w.val}) j w.val).det = 0 := by
        intro w hwne
        by_cases hwk : A w.val k = 0
        · simp [hwk]
        · have hbk : (patternGraph A).Adj w.val k :=
            patternGraph_adj_of_entry (by rintro rfl; exact hk w.2) hwk
          have hminor0 : (almostPrincipal A (S \ {w.val}) j w.val).det = 0 := by
            rw [almostPrincipal_det hA _
                (by intro hh; exact hj (Finset.mem_sdiff.mp hh).1) (by simp),
              schurEntry_eq_zero_of_forall_path hA _
                (by intro hh; exact hj (Finset.mem_sdiff.mp hh).1) (by simp)
                (by rintro rfl; exact hj w.2) (Ne.symm hjk)
                (by rintro rfl; exact hk w.2)
                (by intro hh; exact hk (Finset.mem_sdiff.mp hh).1) ?_, mul_zero]
            intro R
            by_cases hbP : w.val ∈ (P : (patternGraph A).Walk j k).support
            · exfalso
              apply hwne
              have hbQ : w.val ∈ (Q : (patternGraph A).Walk k j).support := by
                rw [hQsupp]; exact List.mem_reverse.mpr hbP
              have htu : ((Q : (patternGraph A).Walk k j).takeUntil w.val hbQ).support
                  = [k, w.val] := by
                have huniq := @Subsingleton.elim _ (hF.subsingleton_path k w.val)
                  (⟨(Q : (patternGraph A).Walk k j).takeUntil w.val hbQ, Q.2.takeUntil hbQ⟩ :
                    (patternGraph A).Path k w.val)
                  ⟨(hbk.symm).toWalk, (hbk.symm).isPath_toWalk⟩
                have h2 := congrArg
                  (fun p : (patternGraph A).Path k w.val =>
                    (p : (patternGraph A).Walk k w.val).support) huniq
                exact h2
              have hpre := SimpleGraph.Walk.support_takeUntil_prefix_support
                (Q : (patternGraph A).Walk k j) hbQ
              rw [htu, hQsupp2] at hpre
              obtain ⟨t, ht⟩ := hpre
              have hw' : w'.support = vr :: w'.support.tail := by
                cases w' with
                | nil => rfl
                | cons h' w'' => rfl
              rw [hw'] at ht
              exact (List.cons.inj (List.cons.inj ht).2).1
            · have hnd : ((P : (patternGraph A).Walk j k).append
                    (hbk.symm).toWalk).support.Nodup := by
                rw [SimpleGraph.Walk.support_append]
                have htail : ((hbk.symm).toWalk).support.tail = [w.val] := rfl
                rw [htail, List.nodup_append]
                refine ⟨P.2.support_nodup, List.nodup_singleton _, ?_⟩
                exact fun x (hx : x ∈ (P : (patternGraph A).Walk j k).support)
                  y (hy : y ∈ [w.val]) (hxy : x = y) => by
                  have h2 : y = w.val := List.mem_singleton.mp hy
                  subst h2
                  subst hxy
                  exact hbP hx
              obtain ⟨hP4, hk4⟩ : ∃ p : (patternGraph A).Path j w.val,
                  k ∈ (p : (patternGraph A).Walk j w.val).support := by
                refine ⟨⟨(P : (patternGraph A).Walk j k).append (hbk.symm).toWalk,
                  SimpleGraph.Walk.IsPath.mk' hnd⟩, ?_⟩
                exact (SimpleGraph.Walk.mem_support_append_iff _ _).mpr
                  (Or.inl (P : (patternGraph A).Walk j k).end_mem_support)
              rw [@Subsingleton.elim _ (hF.subsingleton_path j w.val) R hP4]
              exact hk4
          simp [hminor0]
      rw [almostPrincipal_det_expansion]
      by_cases hvrj : vr = j
      · rw [hvrj] at hadjQ
        have hAjk : A j k ≠ 0 := patternGraph_adj_entry hA hadjQ.symm
        have hD : (A.submatrix (Subtype.val : ↥S → Fin n) Subtype.val).det ≠ 0 :=
          (hA.submatrix Subtype.val_injective).det_pos.ne'
        have hsum0 : (∑ w : ↥S, A w.val k
            * (almostPrincipal A (S \ {w.val}) j w.val).det) = 0 := by
          apply Finset.sum_eq_zero
          intro w _
          apply hbranch
          rintro rfl
          rw [← hvrj] at hj
          exact hj w.2
        rw [hsum0, sub_zero]
        exact mul_ne_zero hAjk hD
      · have hvrS : vr ∈ S := by
          rcases hPsub vr hvrP with hh | hh | hh
          · exact absurd hh hvrj
          · exact absurd hh hvrk
          · exact hh
        have hAjk0 : A j k = 0 := by
          by_contra hne
          have hadj : (patternGraph A).Adj j k :=
            patternGraph_adj_of_entry hjk hne
          have huniq := @Subsingleton.elim _ (hF.subsingleton_path j k)
            (⟨hadj.toWalk, hadj.isPath_toWalk⟩ : (patternGraph A).Path j k) P
          have h2 := congrArg
            (fun p : (patternGraph A).Path j k =>
              (p : (patternGraph A).Walk j k).support) huniq
          have h3 : vr ∈ hadj.toWalk.support := h2.symm ▸ hvrP
          have h4 : hadj.toWalk.support = [j, k] := rfl
          rw [h4] at h3
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
          rcases h3 with hh | hh
          · exact hvrj hh
          · exact hvrk hh
        have hsum : (∑ w : ↥S, A w.val k
              * (almostPrincipal A (S \ {w.val}) j w.val).det)
            = A vr k * (almostPrincipal A (S \ {vr}) j vr).det :=
          Finset.sum_eq_single ⟨vr, hvrS⟩
            (fun w _ hwne => hbranch w (fun hh => hwne (Subtype.ext hh)))
            (by simp)
        rw [hAjk0, hsum]
        have hAvr : A vr k ≠ 0 := patternGraph_adj_entry hA hadjQ.symm
        have hminor : (almostPrincipal A (S \ {vr}) j vr).det ≠ 0 := by
          apply ih (S \ {vr}) ?_ j vr
            (by intro hh; exact hj (Finset.mem_sdiff.mp hh).1) (by simp)
            (by rintro rfl; exact hj hvrS) ?_
          · have hcard : (S \ {vr}).card = S.card - 1 := by
              have hinter : ({vr} ∩ S : Finset (Fin n)) = {vr} := by simp [hvrS]
              rw [Finset.card_sdiff, hinter, Finset.card_singleton]
            have h1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨vr, hvrS⟩
            omega
          · refine ⟨w'.reverse, ?_⟩
            intro x hx
            have hxw' : x ∈ w'.support := by
              rw [SimpleGraph.Walk.support_reverse] at hx
              exact List.mem_reverse.mp hx
            have hxQ : x ∈ (Q : (patternGraph A).Walk k j).support := by
              rw [hQsupp2]; exact List.mem_cons_of_mem _ hxw'
            have hxP : x ∈ (P : (patternGraph A).Walk j k).support := by
              rw [hQsupp] at hxQ; exact List.mem_reverse.mp hxQ
            have hxk : x ≠ k := fun hh => hknodup (hh ▸ hxw')
            rcases hPsub x hxP with hh | hh | hh
            · exact Or.inl hh
            · exact (hxk hh).elim
            · by_cases hxv : x = vr
              · exact Or.inr (Or.inl hxv)
              · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨hh, by simp [hxv]⟩))
        simp only [zero_mul, zero_sub]
        exact neg_ne_zero.mpr (mul_ne_zero hAvr hminor)




/-- `forest_clean`: if `G_A` is a forest then every ordering is clean
(paper Theorem 4.1, `thm:forest`). The proof is the Jones–West
determinant formula: at a predicted position the unique path forces
the almost-principal minor, hence the Schur entry, to be nonzero. -/
theorem forest_clean {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hF : (patternGraph A).IsAcyclic) (σ : List (Fin n))
    (hσ : IsOrdering σ) : IsCleanOrdering A σ := by
  classical
  intro j k hPred
  have hAdj : (fillGraph A σ).Adj j k := hPred
  have hjk : j ≠ k := hAdj.ne
  have hpath : HasPathThrough (patternGraph A) (prefixSet σ j k) j k :=
    ((fill_path σ hσ j k hjk).2).mp (((fill_path σ hσ j k hjk).1).mp hAdj)
  have hj : j ∉ prefixSet σ j k := by
    intro hj
    rw [prefixSet, prefixList, List.mem_toFinset] at hj
    have h2 : j ≠ j ∧ j ≠ k := of_decide_eq_true
      (List.mem_takeWhile_imp (p := fun x => decide (x ≠ j ∧ x ≠ k)) (l := σ) hj)
    exact h2.1 rfl
  have hk : k ∉ prefixSet σ j k := by
    intro hk
    rw [prefixSet, prefixList, List.mem_toFinset] at hk
    have h2 : k ≠ j ∧ k ≠ k := of_decide_eq_true
      (List.mem_takeWhile_imp (p := fun x => decide (x ≠ j ∧ x ≠ k)) (l := σ) hk)
    exact h2.2 rfl
  have hdet := almostPrincipal_det_ne_zero hA hF (prefixSet σ j k).card
    (prefixSet σ j k) le_rfl j k hj hk hjk hpath
  rw [almostPrincipal_det hA (prefixSet σ j k) hj hk] at hdet
  have hD : (0 : ℝ) < (A.submatrix
      (Subtype.val : ↥(prefixSet σ j k) → Fin n) Subtype.val).det :=
    (hA.submatrix Subtype.val_injective).det_pos
  exact fun h => hdet (by rw [h, mul_zero])

end CholeskyCancellations

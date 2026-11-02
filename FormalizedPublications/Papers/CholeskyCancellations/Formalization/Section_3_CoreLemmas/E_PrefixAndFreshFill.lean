/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Logic.Relation
import Mathlib.Analysis.LocallyConvex.Separation
import Section_3_CoreLemmas.D_UniversalAndRefill

/-! # Prefix lemma and fresh fill (paper Section 3)

The prefix lemma, triangle necessity, fresh fill and its closure, and the Nesting Lemma (paper Lemma 3.14). Split from `CoreLemmas.lean`.
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as `Defs.lean` — entries only through `schurEntry`, levels as finsets with enumerating lists wherever the symbolic graph `G_S` is read, cancellations only through `Zeroes`/`logMag`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- `prefix_lemma`: the Prefix Lemma (paper Lemma 3.10, `lem:prefix`): a
zero at a level-predicted position has a witness in the eliminated
set adjacent to both ends one level earlier. Proved by snoc
induction on the elimination list: at the last pivot `v`, either
the edge was created through `v`, or it was already game-adjacent
one level earlier — where a zero entry recurses and a nonzero entry
forces nonzero legs through `v` by the quotient rule. -/
theorem prefix_lemma (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (l : List (Fin n)) (S : Finset (Fin n)) (henum : Enumerates l S)
    (j k : Fin n) (hj : j ∉ S) (hk : k ∉ S)
    (hz : schurEntry A S j k = 0)
    (hg : (gameGraph (patternGraph A) l).Adj j k) :
    ∃ v ∈ S, ∃ l' : List (Fin n), Enumerates l' (S.erase v) ∧
      (gameGraph (patternGraph A) l').Adj j v ∧
      (gameGraph (patternGraph A) l').Adj k v := by
  induction l using List.reverseRecOn generalizing S j k with
  | nil =>
    have hS : S = ∅ := by
      have h2 := henum.2
      simp at h2
      exact h2.symm
    rw [hS, schurEntry_empty] at hz
    have hadj : j ≠ k ∧ (A j k ≠ 0 ∨ A k j ≠ 0) := by
      simpa [gameGraph, patternGraph, SimpleGraph.fromRel_adj] using hg
    rcases hadj.2 with h | h
    · exact (h hz).elim
    · rw [posDef_apply_comm hA] at h
      exact (h hz).elim
  | append_singleton l₀ v ih =>
    obtain ⟨hnd0, -, hdisj⟩ := List.nodup_append.mp henum.1
    have hvnot : v ∉ l₀ := fun hv =>
      (hdisj v hv v (List.mem_singleton_self v)) rfl
    have hvS' : v ∉ l₀.toFinset := by
      simpa [List.mem_toFinset] using hvnot
    have hSeq : S = insert v l₀.toFinset := by
      rw [← henum.2]
      ext x
      simp
    have henum0 : Enumerates l₀ l₀.toFinset := ⟨hnd0, rfl⟩
    have hj0 : j ∉ l₀.toFinset := by
      rw [hSeq] at hj
      exact fun h => hj (Finset.mem_insert_of_mem h)
    have hk0 : k ∉ l₀.toFinset := by
      rw [hSeq] at hk
      exact fun h => hk (Finset.mem_insert_of_mem h)
    have hjI : j ∉ insert v l₀.toFinset := hSeq ▸ hj
    have hkI : k ∉ insert v l₀.toFinset := hSeq ▸ hk
    have hG : gameGraph (patternGraph A) (l₀ ++ [v])
        = elimStep (gameGraph (patternGraph A) l₀) v := by
      simp [gameGraph, List.foldl_append]
    rw [hG] at hg
    -- the last step either already had the edge or created it via v
    have hcases : (gameGraph (patternGraph A) l₀).Adj j k ∨
        ((gameGraph (patternGraph A) l₀).Adj j v ∧
          (gameGraph (patternGraph A) l₀).Adj k v) := by
      have hadj : j ≠ k ∧
          (((gameGraph (patternGraph A) l₀).Adj j k ∨
              ((gameGraph (patternGraph A) l₀).Adj j v ∧
                (gameGraph (patternGraph A) l₀).Adj k v)) ∨
            ((gameGraph (patternGraph A) l₀).Adj k j ∨
              ((gameGraph (patternGraph A) l₀).Adj k v ∧
                (gameGraph (patternGraph A) l₀).Adj j v))) := by
        simpa [elimStep, SimpleGraph.fromRel_adj] using hg
      rcases hadj.2 with (h | h) | (h | h)
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inl h.symm
      · exact Or.inr ⟨h.2, h.1⟩
    have hwit_v : ∀ (h1 : (gameGraph (patternGraph A) l₀).Adj j v)
        (h2 : (gameGraph (patternGraph A) l₀).Adj k v),
        ∃ v ∈ S, ∃ l' : List (Fin n), Enumerates l' (S.erase v) ∧
          (gameGraph (patternGraph A) l').Adj j v ∧
          (gameGraph (patternGraph A) l').Adj k v := by
      intro h1 h2
      refine ⟨v, by rw [hSeq]; exact Finset.mem_insert_self v _, l₀, ?_, h1, h2⟩
      rw [hSeq, Finset.erase_insert hvS']
      exact henum0
    rcases hcases with hadj0 | ⟨hlegj, hlegk⟩
    · by_cases hM : schurEntry A l₀.toFinset j k = 0
      · obtain ⟨w, hwS', l₁, henum1, hleg1, hleg2⟩ :=
          ih l₀.toFinset henum0 j k hj0 hk0 hM hadj0
        have hwv : w ≠ v := fun h => hvS' (h ▸ hwS')
        have hwS : w ∈ S := by
          rw [hSeq]; exact Finset.mem_insert_of_mem hwS'
        have hvnot1 : v ∉ l₁ := by
          intro hv1
          have : v ∈ l₁.toFinset := by simpa [List.mem_toFinset] using hv1
          rw [henum1.2] at this
          exact hvS' (Finset.mem_of_mem_erase this)
        refine ⟨w, hwS, l₁ ++ [v], ?_, ?_, ?_⟩
        · constructor
          · exact List.nodup_append.mpr ⟨henum1.1, by simp,
              fun x hx b hb => by
                rw [List.mem_singleton] at hb
                intro hxb
                exact hvnot1 ((hxb.trans hb) ▸ hx)⟩
          · have h1 : (l₁ ++ [v]).toFinset = insert v l₁.toFinset := by
              ext x; simp
            rw [h1, henum1.2]
            ext x
            by_cases hxw : x = w
            · simp [hxw, hwv]
            · by_cases hxv : x = v
              · simp [hxv, hSeq, show v ≠ w from Ne.symm hwv]
              · simp [hSeq, hxw, hxv]
        · exact gameGraph_adj_mono_append _ l₁ [v] j w hleg1
        · exact gameGraph_adj_mono_append _ l₁ [v] k w hleg2
      · -- entry at S' nonzero, but zero after pivoting at v: legs nonzero
        have hz' : schurEntry A (insert v l₀.toFinset) j k = 0 := hSeq ▸ hz
        rw [schur_quotient hA l₀.toFinset v hvS' j k hjI hkI] at hz'
        unfold pivotEntry at hz'
        have hvv : schurEntry A l₀.toFinset v v ≠ 0 :=
          ne_of_gt (schurEntry_pos hA _ hvS')
        have hprod : schurEntry A l₀.toFinset j v
            * schurEntry A l₀.toFinset k v ≠ 0 := by
          intro hp
          rw [hp] at hz'
          simp only [zero_div, sub_zero] at hz'
          exact hM hz'
        obtain ⟨hjv, hkv⟩ := mul_ne_zero_iff.mp hprod
        have hjne : j ≠ v :=
          fun h => hjI (by rw [h]; exact Finset.mem_insert_self v _)
        have hkne : k ≠ v :=
          fun h => hkI (by rw [h]; exact Finset.mem_insert_self v _)
        exact hwit_v
          (numeric_le_gameGraph hA l₀ j v
            (numericPattern_adj_mk _ j v hjne hjv))
          (numeric_le_gameGraph hA l₀ k v
            (numericPattern_adj_mk _ k v hkne hkv))
    · exact hwit_v hlegj hlegk



/-- `triangle_necessary`: only an edge in a fill-graph triangle
can cancel (paper Corollary 3.11, `cor:tri-nec`). Proved: the
Prefix Lemma supplies the third vertex; extending its enumeration
to the ordering `l' ++ v :: t` puts the legs at their committing
prefixes, and the cancelled edge is fill-adjacent there by the path
characterization (`level_graph_path`). -/
theorem triangle_necessary (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (l : List (Fin n)) (S : Finset (Fin n))
    (henum : Enumerates l S) (j k : Fin n) (hj : j ∉ S) (hk : k ∉ S)
    (hz : schurEntry A S j k = 0)
    (hg : (gameGraph (patternGraph A) l).Adj j k) :
    ∃ (v : Fin n), v ∈ S ∧ ∃ (σ : List (Fin n)), IsOrdering σ ∧
      (fillGraph A σ).IsClique ({j, k, v} : Set (Fin n)) := by
  obtain ⟨v, hvS, l', henum', hlegj, hlegk⟩ :=
    prefix_lemma A hA l S henum j k hj hk hz hg
  have hjk : j ≠ k := hg.ne
  have htake_all : ∀ (l₀ t : List (Fin n)) (a b : Fin n),
      (∀ x ∈ l₀, x ≠ a ∧ x ≠ b) →
        (l₀ ++ t).takeWhile (fun x => x ≠ a ∧ x ≠ b)
          = l₀ ++ t.takeWhile (fun x => x ≠ a ∧ x ≠ b) := by
    intro l₀
    induction l₀ with
    | nil => intro t a b _; rfl
    | cons y l₀ ih =>
      intro t a b hall
      have hy : y ≠ a ∧ y ≠ b := hall y (List.mem_cons_self)
      have ih' := ih t a b (fun x hx => hall x (List.mem_cons_of_mem y hx))
      rw [List.cons_append, List.takeWhile_cons_of_pos (by
        show decide (y ≠ a ∧ y ≠ b) = true
        rw [decide_eq_true_eq]; exact hy), List.cons_append, ih']
  have htake_stop : ∀ (l₀ t : List (Fin n)) (a b : Fin n),
      (∀ x ∈ l₀, x ≠ a ∧ x ≠ b) →
        (l₀ ++ b :: t).takeWhile (fun x => x ≠ a ∧ x ≠ b) = l₀ := by
    intro l₀ t a b hall
    rw [htake_all l₀ (b :: t) a b hall,
      List.takeWhile_cons_of_neg (by simp), List.append_nil]
  obtain ⟨t, htS, htnd⟩ : ∃ t : List (Fin n), t.toFinset = Sᶜ ∧ t.Nodup :=
    ⟨Sᶜ.sort (· ≤ ·), Finset.sort_toFinset _ _, Finset.sort_nodup _ _⟩
  have hl'mem : ∀ x ∈ l', x ∈ S.erase v := by
    intro x hx
    have hx' : x ∈ l'.toFinset := by simpa [List.mem_toFinset] using hx
    rwa [henum'.2] at hx'
  have hvnot : v ∉ l' := by
    intro hv
    have hv' := hl'mem v hv
    exact (Finset.mem_erase.mp hv').1 rfl
  have hvnot_t : v ∉ t := by
    intro hv
    have hv' : v ∈ t.toFinset := by simpa [List.mem_toFinset] using hv
    rw [htS, Finset.mem_compl] at hv'
    exact hv' hvS
  refine ⟨v, hvS, l' ++ v :: t, ?_, ?_⟩
  · constructor
    · rw [List.nodup_append]
      refine ⟨henum'.1, ?_, ?_⟩
      · rw [List.nodup_cons]
        exact ⟨hvnot_t, htnd⟩
      · intro x hx y hy hxy
        have hxS : x ∈ S := Finset.mem_of_mem_erase (hl'mem x hx)
        rw [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hvnot (hxy ▸ hx)
        · have hx' : x ∈ t.toFinset := by
            have hyt : y ∈ t.toFinset := by
              simpa [List.mem_toFinset] using hy
            rwa [← hxy] at hyt
          rw [htS, Finset.mem_compl] at hx'
          exact hx' hxS
    · have h1 : l'.length = (S.erase v).card := by
        rw [← List.toFinset_card_of_nodup henum'.1, henum'.2]
      have h2 : t.length = Sᶜ.card := by
        rw [← List.toFinset_card_of_nodup htnd, htS]
      have h3 := Finset.card_erase_add_one hvS
      have h4 := Finset.card_compl S
      have h5 : Fintype.card (Fin n) = n := Fintype.card_fin n
      have h6 := Finset.card_le_univ S
      simp only [List.length_append, List.length_cons, h1, h2]
      omega
  · set σ := l' ++ v :: t with hσdef
    have hσform : σ = (l' ++ [v]) ++ t := by
      rw [hσdef]
      exact (List.append_assoc l' [v] t).symm
    have hall_jv : ∀ x ∈ l', x ≠ j ∧ x ≠ v := by
      intro x hx
      have hxS := hl'mem x hx
      exact ⟨fun h => hj (h ▸ Finset.mem_of_mem_erase hxS),
        (Finset.mem_erase.mp hxS).1⟩
    have hall_kv : ∀ x ∈ l', x ≠ k ∧ x ≠ v := by
      intro x hx
      have hxS := hl'mem x hx
      exact ⟨fun h => hk (h ▸ Finset.mem_of_mem_erase hxS),
        (Finset.mem_erase.mp hxS).1⟩
    have hpre_jv : prefixList σ j v = l' := by
      rw [prefixList, hσdef]
      exact htake_stop l' t j v hall_jv
    have hpre_kv : prefixList σ k v = l' := by
      rw [prefixList, hσdef]
      exact htake_stop l' t k v hall_kv
    have hFjv : (fillGraph A σ).Adj j v := by
      rw [fillGraph_adj_iff, hpre_jv]; exact hlegj
    have hFkv : (fillGraph A σ).Adj k v := by
      rw [fillGraph_adj_iff, hpre_kv]; exact hlegk
    have hFjk : (fillGraph A σ).Adj j k := by
      rw [fillGraph_adj_iff]
      have henumS : Enumerates (l' ++ [v]) S := by
        constructor
        · rw [List.nodup_append]
          refine ⟨henum'.1, by simp, fun x hx b hb hxb => ?_⟩
          rw [List.mem_singleton] at hb
          exact hvnot ((hxb.trans hb) ▸ hx)
        · ext x
          simp only [List.mem_toFinset, List.mem_append, List.mem_singleton]
          constructor
          · rintro (hx | rfl)
            · have : x ∈ l'.toFinset := by
                simpa [List.mem_toFinset] using hx
              rw [henum'.2] at this
              exact Finset.mem_of_mem_erase this
            · exact hvS
          · intro hx
            by_cases hxv : x = v
            · exact Or.inr hxv
            · refine Or.inl ?_
              have : x ∈ S.erase v := Finset.mem_erase.mpr ⟨hxv, hx⟩
              rw [← henum'.2] at this
              simpa [List.mem_toFinset] using this
      have hpath : HasPathThrough (patternGraph A) S j k :=
        (level_graph_path l S henum j k hj hk hjk).mp hg
      have hadjv : (gameGraph (patternGraph A) (l' ++ [v])).Adj j k :=
        (level_graph_path (l' ++ [v]) S henumS j k hj hk hjk).mpr hpath
      have hall_jk : ∀ x ∈ l' ++ [v], x ≠ j ∧ x ≠ k := by
        intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · have hxS := Finset.mem_of_mem_erase (hl'mem x hx)
          exact ⟨fun h => hj (h ▸ hxS), fun h => hk (h ▸ hxS)⟩
        · rw [List.mem_singleton] at hx
          exact ⟨fun h => hj ((hx.symm.trans h) ▸ hvS),
            fun h => hk ((hx.symm.trans h) ▸ hvS)⟩
      have hpre_eq : prefixList σ j k
          = (l' ++ [v]) ++ t.takeWhile (fun x => x ≠ j ∧ x ≠ k) := by
        rw [prefixList, hσform]
        exact htake_all (l' ++ [v]) t j k hall_jk
      rw [hpre_eq]
      exact gameGraph_adj_mono_append _ (l' ++ [v]) _ j k hadjv
    have s1 := hFjv.symm; have s2 := hFkv.symm; have s3 := hFjk.symm
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl <;>
      first | contradiction | assumption



/-- `fresh_fill`: fresh fill is nonzero when created (paper
Lemma 3.12, `lem:fresh`), with its displayed value. Proved: no game
edge at level `S` forces a zero entry there by
`numeric_le_gameGraph`, and the quotient rule at `v` then computes
the fresh value. -/
theorem fresh_fill (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (l : List (Fin n)) (S : Finset (Fin n)) (henum : Enumerates l S)
    (v j k : Fin n) (hv : v ∉ S) (hj : j ∉ insert v S)
    (hk : k ∉ insert v S) (hjk : j ≠ k)
    (_hjv : (gameGraph (patternGraph A) l).Adj j v)
    (_hkv : (gameGraph (patternGraph A) l).Adj k v)
    (hnk : ¬ (gameGraph (patternGraph A) l).Adj j k) :
    schurEntry A S j k = 0 ∧
    schurEntry A (insert v S) j k
      = - (schurEntry A S j v * schurEntry A S k v
          / schurEntry A S v v) ∧
    (schurEntry A S j v ≠ 0 → schurEntry A S k v ≠ 0 →
      schurEntry A (insert v S) j k ≠ 0) := by
  have hS : l.toFinset = S := henum.2
  have h0 : schurEntry A S j k = 0 := by
    by_contra hne
    apply hnk
    rw [← hS] at hne
    exact numeric_le_gameGraph hA l j k
      (numericPattern_adj_mk _ j k hjk hne)
  have hval : schurEntry A (insert v S) j k
      = - (schurEntry A S j v * schurEntry A S k v
          / schurEntry A S v v) := by
    rw [schur_quotient hA S v hv j k hj hk]
    simp [pivotEntry, h0]
  refine ⟨h0, hval, ?_⟩
  intro hjv hkv
  rw [hval]
  exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hjv hkv)
    (ne_of_gt (schurEntry_pos hA S hv)))



/-- `fresh_fill_closure`: the closure form of fresh fill (paper
Corollary 3.13, `cor:fresh-closure`), with "active slot" read as its
defining entry equation. Proved from the same two steps as
`fresh_fill`: a zero after pivoting at `v` forces a zero leg. -/
theorem fresh_fill_closure (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (l : List (Fin n)) (S : Finset (Fin n))
    (henum : Enumerates l S) (v j k : Fin n) (hv : v ∉ S)
    (hj : j ∉ insert v S) (hk : k ∉ insert v S) (hjk : j ≠ k)
    (_hjv : (gameGraph (patternGraph A) l).Adj j v)
    (_hkv : (gameGraph (patternGraph A) l).Adj k v)
    (hnk : ¬ (gameGraph (patternGraph A) l).Adj j k)
    (hz : schurEntry A (insert v S) j k = 0) :
    schurEntry A S j v = 0 ∨ schurEntry A S k v = 0 := by
  have hS : l.toFinset = S := henum.2
  have h0 : schurEntry A S j k = 0 := by
    by_contra hne
    apply hnk
    rw [← hS] at hne
    exact numeric_le_gameGraph hA l j k
      (numericPattern_adj_mk _ j k hjk hne)
  rw [schur_quotient hA S v hv j k hj hk] at hz
  unfold pivotEntry at hz
  rw [h0] at hz
  simp only [zero_sub, neg_eq_zero, div_eq_zero_iff, mul_eq_zero] at hz
  rcases hz with (h | h) | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (ne_of_gt (schurEntry_pos hA S hv))



/-- The Nesting Lemma (paper Lemma 3.14, `lem:nesting`): a pair
zero at two consecutive levels has a zero leg at the first of them. -/
theorem nesting (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (S : Finset (Fin n)) (i j k : Fin n)
    (hi : i ∉ S) (hj : j ∉ S) (hk : k ∉ S) (hij : i ≠ j) (hik : i ≠ k)
    (_hjk : j ≠ k) (h0 : schurEntry A S j k = 0)
    (h1 : schurEntry A (insert i S) j k = 0) :
    schurEntry A S j i = 0 ∨ schurEntry A S k i = 0 := by
  have hjI : j ∉ insert i S := by simp [Ne.symm hij, hj]
  have hkI : k ∉ insert i S := by simp [Ne.symm hik, hk]
  rw [schur_quotient hA S i hi j k hjI hkI] at h1
  unfold pivotEntry at h1
  rw [h0] at h1
  simp only [zero_sub, neg_eq_zero, div_eq_zero_iff] at h1
  rcases h1 with h1 | h1
  · rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  · exact absurd h1 (ne_of_gt (schurEntry_pos hA S hi))

end CholeskyCancellations

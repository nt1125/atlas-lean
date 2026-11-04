/-
Copyright (c) 2026 Nam Trang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Trang
-/

import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Logic.Relation
import Mathlib.Analysis.LocallyConvex.Separation
import Section_3_CoreLemmas.E_PrefixAndFreshFill

/-! # Cycles and monotonicity (paper Section 3)

Same-pair bookkeeping, the arc digraph, general cycles, four-cycles (and infeasibility), and the Monotone Lemma (paper Lemma 3.18).
-/

namespace CholeskyCancellations

/- Spine-choice comment (MANDATORY per theory file): same single spine as the Section 2 files — entries only through `schurEntry`, levels as finsets with enumerating lists wherever the symbolic graph `G_S` is read, cancellations only through `Zeroes`/`logMag`. (Plain comment: a docstring cannot precede `variable`.) -/
variable {n : ℕ}


/-- `NonzeroPairs A S`: ordered representatives of the survivor
pairs nonzero in `A/A_S` — the vertices of the arc digraph (paper
Definition 3.15, `def:arcdigraph`). Bridge: the paper's vertices are
unordered pairs `{j, k}`; each appears here in both orders, and the
arc relation below is blind to the order chosen. -/
def NonzeroPairs (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : Type :=
  {p : Fin n × Fin n // p.1 ∉ S ∧ p.2 ∉ S ∧ p.1 ≠ p.2 ∧
    schurEntry A S p.1 p.2 ≠ 0}



/-- `SamePair x y u v`: `(x, y)` and `(u, v)` name the same unordered
pair (used by `arcDigraph`, paper Definition 3.15). -/
def SamePair (x y u v : Fin n) : Prop :=
  (x = u ∧ y = v) ∨ (x = v ∧ y = u)



/-- `arcDigraph A S H`: the arc digraph `D(H)` (paper
Definition 3.15, `def:arcdigraph`): an imposed relation
`t⁽ˢ⁾_{jk} = t⁽ˢ⁾_{ji} + t⁽ˢ⁾_{ki}` contributes the arcs
`{j, k} → {j, i}` and `{j, k} → {k, i}` between nonzero pairs. -/
noncomputable def arcDigraph (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (H : Set (Slot n)) : Digraph (NonzeroPairs A S) :=
  ⟨fun a b => ∃ s ∈ H, ∃ v : Fin n, s.level = insert v S ∧ v ∉ S ∧
    SamePair a.1.1 a.1.2 s.fst s.snd ∧
      (SamePair b.1.1 b.1.2 s.fst v ∨ SamePair b.1.1 b.1.2 s.snd v)⟩



/-- The General Cycle Lemma (paper Lemma 3.16, `lem:cycle`): a
directed cycle in `D(H)` makes `H` infeasible. A directed cycle is a
vertex reachable from itself in at least one arc step
(`Relation.TransGen`); each arc strictly decreases any feasible
positive symmetric `t`. The conclusion is formal-system
infeasibility (`¬ IsFeasibleAt`, see its docstring): the proof's
chain of strict inequalities uses only the equations of the
slots appearing as arcs. Each arc witnesses one leg nonzero
(its target pair is a nonzero pair); the other leg's
contribution is positive because the formal `t` is positive on
every pair by definition. In the paper's argument both legs are
nonzero, so both paper `t` values are finite and positive;
that is the difference between the formal-system conclusion
here and the paper's infeasibility. -/
theorem general_cycle (A : Matrix (Fin n) (Fin n) ℝ) (_hA : A.PosDef)
    (S : Finset (Fin n)) (H : Set (Slot n))
    (_hslots : ∀ s ∈ H, ∃ v : Fin n, v ∉ S ∧ s.level = insert v S)
    (hcycle : ∃ a : NonzeroPairs A S,
      Relation.TransGen (arcDigraph A S H).Adj a a) :
    ¬ IsFeasibleAt H S := by
  rintro ⟨t, htpos, htsymm, hteq⟩
  obtain ⟨a, hcyc⟩ := hcycle
  have hval : ∀ p : NonzeroPairs A S, ∀ x y : Fin n,
      SamePair p.1.1 p.1.2 x y → t p.1.1 p.1.2 = t x y := by
    intro p x y hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
    · rfl
    · rw [h1, h2, htsymm]
  have harclt : ∀ x y : NonzeroPairs A S,
      (arcDigraph A S H).Adj x y → t y.1.1 y.1.2 < t x.1.1 x.1.2 := by
    intro x y hxy
    obtain ⟨s, hsH, v, hlevel, hvS, hsrc, htgt⟩ := hxy
    obtain ⟨v', hlevel', _hv'S, heqs⟩ := hteq s hsH
    have hvv : v = v' := by
      have hmem : v ∈ insert v' S := by
        have hins : insert v S = insert v' S := by rw [← hlevel, ← hlevel']
        rw [← hins]
        exact Finset.mem_insert_self v S
      rcases Finset.mem_insert.mp hmem with h | h
      · exact h
      · exact absurd h hvS
    subst hvv
    rw [hval x s.fst s.snd hsrc]
    rcases htgt with htgt | htgt
    · rw [hval y s.fst v htgt, heqs, htsymm s.fst v]
      have hpos := htpos v s.snd
      linarith
    · rw [hval y s.snd v htgt, heqs, htsymm s.snd v]
      have hpos := htpos v s.fst
      linarith
  have hlt : ∀ {x y : NonzeroPairs A S},
      Relation.TransGen (arcDigraph A S H).Adj x y →
        t y.1.1 y.1.2 < t x.1.1 x.1.2 := by
    intro x y h
    induction h with
    | single h => exact harclt _ _ h
    | tail _h₁ h₂ ih => exact lt_trans (harclt _ _ h₂) ih
  exact lt_irrefl _ (hlt hcyc)



/-- The 4-cycle Lemma (paper Lemma 3.17, `lem:4cycle`): the four
displayed additive relations, transcribed with the paper's index
orders, cannot hold simultaneously. The paper takes four distinct
survivors; only the two cross-pair distinctness facts the proof
uses are assumed. All their pairs are assumed nonzero, so every log-magnitude written is the paper's
finite `t⁽ˢ⁾` value. Summing the four relations against symmetry
forces a positive sum to vanish. -/
theorem four_cycle (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (S : Finset (Fin n)) (a b c d : Fin n)
    (ha : a ∉ S) (hb : b ∉ S) (hc : c ∉ S) (hd : d ∉ S)
    (hac : a ≠ c) (hbd : b ≠ d)
    (hne : ∀ x ∈ ({a, b, c, d} : Finset (Fin n)),
      ∀ y ∈ ({a, b, c, d} : Finset (Fin n)), x ≠ y →
        schurEntry A S x y ≠ 0) :
    ¬ (logMag A S a b = logMag A S a c + logMag A S b c
      ∧ logMag A S b c = logMag A S b d + logMag A S c d
      ∧ logMag A S c d = logMag A S c a + logMag A S d a
      ∧ logMag A S d a = logMag A S d b + logMag A S a b) := by
  rintro ⟨h1, h2, h3, h4⟩
  have hpa : 0 < logMag A S a c :=
    logMag_pos hA S ha hc hac (hne a (by simp) c (by simp) hac)
  have hpb : 0 < logMag A S b d :=
    logMag_pos hA S hb hd hbd (hne b (by simp) d (by simp) hbd)
  have hs1 : logMag A S c a = logMag A S a c := logMag_symm hA S c a
  have hs2 : logMag A S d b = logMag A S b d := logMag_symm hA S d b
  linarith



/-- The 4-cycle Lemma in its formal-system form (paper Lemma 3.17,
`lem:4cycle`): the four apex slots of a 4-cycle of survivors form
a formally infeasible family at level `S` (`¬ IsFeasibleAt`,
see its docstring: the paper's relations are imposed only when
the legs are nonzero). The paper's statement, with all pairs
nonzero so that Lemma 2.33 supplies all four relations, is the
matrix form `four_cycle`. -/
theorem four_cycle_infeasible {S : Finset (Fin n)} {a b c d : Fin n}
    (ha : a ∉ S) (hb : b ∉ S) (hc : c ∉ S) (hd : d ∉ S)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ¬ IsFeasibleAt
      {⟨insert c S, a, b,
          (by rw [Finset.mem_insert]; push Not; exact ⟨hac, ha⟩),
          (by rw [Finset.mem_insert]; push Not; exact ⟨hbc, hb⟩), hab⟩,
        ⟨insert d S, b, c,
          (by rw [Finset.mem_insert]; push Not; exact ⟨hbd, hb⟩),
          (by rw [Finset.mem_insert]; push Not; exact ⟨hcd, hc⟩), hbc⟩,
        ⟨insert a S, c, d,
          (by rw [Finset.mem_insert]; push Not; exact ⟨fun h => hac h.symm, hc⟩),
          (by rw [Finset.mem_insert]; push Not; exact ⟨fun h => had h.symm, hd⟩),
          hcd⟩,
        ⟨insert b S, d, a,
          (by rw [Finset.mem_insert]; push Not; exact ⟨fun h => hbd h.symm, hd⟩),
          (by rw [Finset.mem_insert]; push Not; exact ⟨hab, ha⟩),
          Ne.symm had⟩} S := by
  rintro ⟨t, hpos, hsymm, hslots⟩
  have hvinj : ∀ {v w : Fin n}, insert v S = insert w S → v ∉ S →
      w ∉ S → v = w := by
    intro v w h hv hw
    have h2 : v ∈ insert w S := by
      rw [← h]
      exact Finset.mem_insert_self v S
    rw [Finset.mem_insert] at h2
    rcases h2 with h2 | h2
    · exact h2
    · exact absurd h2 hv
  have key : ∀ (s : Slot n), s ∈
      ({⟨insert c S, a, b,
          (by rw [Finset.mem_insert]; push Not; exact ⟨hac, ha⟩),
          (by rw [Finset.mem_insert]; push Not; exact ⟨hbc, hb⟩), hab⟩,
        ⟨insert d S, b, c,
          (by rw [Finset.mem_insert]; push Not; exact ⟨hbd, hb⟩),
          (by rw [Finset.mem_insert]; push Not; exact ⟨hcd, hc⟩), hbc⟩,
        ⟨insert a S, c, d,
          (by rw [Finset.mem_insert]; push Not; exact ⟨fun h => hac h.symm, hc⟩),
          (by rw [Finset.mem_insert]; push Not; exact ⟨fun h => had h.symm, hd⟩),
          hcd⟩,
        ⟨insert b S, d, a,
          (by rw [Finset.mem_insert]; push Not; exact ⟨fun h => hbd h.symm, hd⟩),
          (by rw [Finset.mem_insert]; push Not; exact ⟨hab, ha⟩),
          Ne.symm had⟩} : Set (Slot n)) →
      ∀ (v : Fin n), s.level = insert v S → v ∉ S →
      t s.fst s.snd = t v s.fst + t v s.snd := by
    intro s hs v hv hvS
    obtain ⟨v', hv1, hv2, hv3⟩ := hslots s hs
    have : v' = v := hvinj (hv1.symm.trans hv) hv2 hvS
    rwa [this] at hv3
  have e1 : t a b = t c a + t c b :=
    key ⟨insert c S, a, b, by simp [hac, ha], by simp [hbc, hb], hab⟩
      (by simp) c rfl hc
  have e2 : t b c = t d b + t d c :=
    key ⟨insert d S, b, c, by simp [hbd, hb], by simp [hcd, hc], hbc⟩
      (by simp) d rfl hd
  have e3 : t c d = t a c + t a d :=
    key ⟨insert a S, c, d, by simp [Ne.symm hac, hc],
      by simp [Ne.symm had, hd], hcd⟩ (by simp) a rfl ha
  have e4 : t d a = t b d + t b a :=
    key ⟨insert b S, d, a, by simp [Ne.symm hbd, hd],
      by simp [hab, ha], Ne.symm had⟩ (by simp) b rfl hb
  have g1 : t b c < t a b := by
    rw [e1, hsymm c a, hsymm c b]
    have := hpos a c
    linarith
  have g2 : t c d < t b c := by
    rw [e2, hsymm d b, hsymm d c]
    have := hpos b d
    linarith
  have g3 : t d a < t c d := by
    rw [e3, hsymm a c, hsymm a d]
    have := hpos c a
    linarith
  have g4 : t a b < t d a := by
    rw [e4, hsymm b d, hsymm b a]
    have := hpos d b
    linarith
  linarith



/-- The Monotone Lemma (paper Lemma 3.18, `lem:monotone`):
unrealizability is inherited by supersets. -/
theorem monotone (G : SimpleGraph (Fin n)) (H H' : Set (Slot n))
    (hHH' : H ⊆ H') (hH : ¬ IsRealizable H G) : ¬ IsRealizable H' G := by
  rintro ⟨A, hA, hG, hact⟩
  exact hH ⟨A, hA, hG, fun s hs => hact s (hHH' hs)⟩

end CholeskyCancellations

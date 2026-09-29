-- Prove2me | solution 1 for EnergyAscent.spine_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T07:44:22.022982+00:00
-- url     : https://prove2.me/submissions/ca0d3c16-10d3-4ee7-a3ba-6bd5f94939a2

import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentFermatWindow
import Definitions.Def_Combinatorics_EnergyAscentPellSpine
open EnergyAscent in
theorem solution (n : ℕ) :
    0 < (spine n).1 ∧ 0 < (spine n).2.1 ∧ 0 < (spine n).2.2 ∧
      IsPT (spine n).1 (spine n).2.1 (spine n).2.2 ∧
      ((spine n).1 - (spine n).2.1) ^ 2 = 1 ∧
      (n : ℤ) + 5 ≤ (spine n).2.2 := by
  induction n with
  | zero =>
    simp only [spine, IsPT]
    norm_num
  | succ n ih =>
    -- the Barning–Hall step `B2` preserves the Pythagorean form and `(a - b)²`, and grows `c`
    obtain ⟨ha, hb, hc, hpt, hd, hn⟩ := ih
    rcases hs : spine n with ⟨a, b, c⟩
    rw [hs] at ha hb hc hpt hd hn
    simp only at ha hb hc hpt hd hn
    have hstep : spine (n + 1) = B2 a b c := by rw [spine, hs]
    rw [hstep]
    simp only [B2]
    unfold IsPT at hpt ⊢
    refine ⟨by linarith, by linarith, by linarith, by linear_combination hpt,
      by linear_combination hd, by push_cast; linarith⟩

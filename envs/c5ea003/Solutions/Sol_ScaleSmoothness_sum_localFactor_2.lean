-- Prove2me | solution 2 for ScaleSmoothness.sum_localFactor
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:48:22.266063+00:00
-- url     : https://prove2.me/submissions/8352d1b2-f027-4bec-a6fc-b1488fb682c6

import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
open ScaleSmoothness Finset in
theorem solution (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∑ N : ZMod p, localFactor p N = (p : ℚ) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp3 : 3 ≤ p := by omega
  -- the fibres of `x ↦ x²` partition `ZMod p`, so the dial values sum to `p`
  have hd : ∑ N : ZMod p, dial p N = p := by
    have h : (Finset.univ : Finset (ZMod p)).card
        = ∑ N ∈ (Finset.univ : Finset (ZMod p)),
          ((Finset.univ : Finset (ZMod p)).filter (fun x => x ^ 2 = N)).card :=
      Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
    simp only [dial]
    rw [← h, Finset.card_univ, ZMod.card]
  have hcast : ∑ N : ZMod p, ((dial p N : ℚ)) = (p : ℚ) := by
    rw [← Nat.cast_sum, hd]
  have hne : ((p : ℚ) - 1) ≠ 0 := by
    have h3 : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
    intro h
    linarith
  simp only [localFactor]
  rw [← Finset.sum_div]
  have hsum : ∑ N : ZMod p, ((p : ℚ) - (dial p N : ℚ)) = (p : ℚ) * (p : ℚ) - (p : ℚ) := by
    rw [Finset.sum_sub_distrib, hcast, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul]
  rw [hsum]
  field_simp

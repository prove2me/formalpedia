-- Prove2me | solution 1 for ShorIrreducible.dvd_mul_iff_cutPeriod_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:16:51.93413+00:00
-- url     : https://prove2.me/submissions/d1b99268-ccd7-45e1-8d0b-03e2021dc662

-- Sol generated from Novelty/ShorCutComplementarity.lean
import Mathlib
import Definitions.Def_Novelty_ShorCutRankSharp

/-! # The corrected input/output law for the two endpoints of the QFT

`ShorCutAlignment.not_complementary_ranks` refutes the naive complementarity
conjecture (`rank_in · rank_out` bounded below by a function of `min(r,m)`).
This file proves the corrected law suggested by that refutation.

The engine is an *order* characterisation of the cut period:
`r ∣ B · k ↔ (r / gcd(r,B)) ∣ k` (`dvd_mul_iff_cutPeriod_dvd`), i.e.
`cutPeriod r B` is the order of the block size `B` in `ℤ/r`.  From it:

* `cutPeriod_lcm` : `cutPeriod (lcm r m) B = lcm (cutPeriod r B) (cutPeriod m B)`
  — the joint cut period is the *lcm* of the two endpoint cut periods, not their
  product and not a complementary divisor pair;
* `schmidtRank_mul_ge` : `min C (cutPeriod (lcm r m) B) ≤ rank_in · rank_out`,
  the corrected complementarity inequality;
* `lcm_dvd_of_both_rank_one` : a cut compresses **both** endpoints only when the
  block size is a multiple of `lcm(r, m)` — so, by `not_dvd_pow_two_of_odd`, never
  for a power-of-two cut of an odd order.
-/

open Finset

open ShorIrreducible

open IITTensorNetwork


variable {B C r m x0 j Q : ℕ} {amp : ℝ}








open ShorIrreducible in
theorem solution(hr : 0 < r) (B k : ℕ) :
    r ∣ B * k ↔ cutPeriod r B ∣ k := by
  have hg : 0 < Nat.gcd r B := Nat.gcd_pos_of_pos_left B hr
  have hrg : Nat.gcd r B * (r / Nat.gcd r B) = r :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left r B)
  have hBg : Nat.gcd r B * (B / Nat.gcd r B) = B :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right r B)
  constructor
  · intro h
    have h1 : Nat.gcd r B * (r / Nat.gcd r B)
        ∣ Nat.gcd r B * ((B / Nat.gcd r B) * k) := by
      rw [hrg, ← mul_assoc, hBg]
      exact h
    have h2 : (r / Nat.gcd r B) ∣ (B / Nat.gcd r B) * k :=
      (mul_dvd_mul_iff_left (by omega : Nat.gcd r B ≠ 0)).mp h1
    have h3 : (r / Nat.gcd r B) ∣ k * (B / Nat.gcd r B) := by
      rwa [mul_comm] at h2
    exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_div_gcd_div_gcd hg) h3
  · rintro ⟨t, rfl⟩
    refine ⟨(B / Nat.gcd r B) * t, ?_⟩
    calc B * (cutPeriod r B * t)
        = (Nat.gcd r B * (B / Nat.gcd r B)) * (cutPeriod r B * t) := by rw [hBg]
      _ = (Nat.gcd r B * cutPeriod r B) * ((B / Nat.gcd r B) * t) := by ring
      _ = r * ((B / Nat.gcd r B) * t) := by rw [cutPeriod, hrg]

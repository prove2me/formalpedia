-- Prove2me | solution 1 for ShorIrreducible.cutPeriod_lcm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:18:55.697527+00:00
-- url     : https://prove2.me/submissions/334c8840-3105-4363-ad90-40330cecf77a

-- Sol generated from Novelty/ShorCutComplementarity.lean
import Mathlib
import Definitions.Def_Novelty_ShorCutRankSharp
import Theorems.Thm_ShorIrreducible_dvd_mul_iff_cutPeriod_dvd

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
theorem solution(hr : 0 < r) (hm : 0 < m) :
    cutPeriod (Nat.lcm r m) B = Nat.lcm (cutPeriod r B) (cutPeriod m B) := by
  have hL : 0 < Nat.lcm r m := Nat.pos_of_ne_zero (by
    simp [Nat.lcm_eq_zero_iff]
    omega)
  refine Nat.dvd_antisymm ?_ ?_
  · refine (dvd_mul_iff_cutPeriod_dvd hL B _).mp (Nat.lcm_dvd ?_ ?_)
    · exact (dvd_mul_iff_cutPeriod_dvd hr B _).mpr (Nat.dvd_lcm_left _ _)
    · exact (dvd_mul_iff_cutPeriod_dvd hm B _).mpr (Nat.dvd_lcm_right _ _)
  · have hLdvd : Nat.lcm r m ∣ B * cutPeriod (Nat.lcm r m) B :=
      (dvd_mul_iff_cutPeriod_dvd hL B _).mpr dvd_rfl
    refine Nat.lcm_dvd ?_ ?_
    · exact (dvd_mul_iff_cutPeriod_dvd hr B _).mp
        (dvd_trans (Nat.dvd_lcm_left r m) hLdvd)
    · exact (dvd_mul_iff_cutPeriod_dvd hm B _).mp
        (dvd_trans (Nat.dvd_lcm_right r m) hLdvd)

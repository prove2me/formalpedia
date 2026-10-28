-- Prove2me | solution 1 for zeta_ne_zero_of_strip_of_hundred_lt_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T11:42:55.537805+00:00
-- url     : https://prove2.me/submissions/4ed61d3b-6a77-4716-b7da-474e29b56a2f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_100_101
import Theorems.Thm_TaoFivePrimes_rh_verified_slice_101_102
import Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_102_103
import Theorems.Thm_TaoFivePrimes_rh_verified_slice_103_104
import Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_104_105
import Theorems.Thm_TaoFivePrimes_rh_verified_slice_105_106
import Theorems.Thm_zeta_ne_zero_of_strip_of_hundred_six_lt_im

open Complex

/-- Reduction of `zeta_ne_zero_of_strip_of_hundred_lt_im`: heights `100 < Im s ≤ 106` are covered
by six certified unit slices (originally proved by raresbuhai in env 0df444a, ported to 777aaa6),
and heights `Im s > 106` are the remaining open (RH-equivalent) child. -/
theorem solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 100 < s.im) : riemannZeta s ≠ 0 := by
  have hpos : 0 < s.re := by linarith
  have hne : s.re ≠ 1 / 2 := by linarith
  by_cases h106 : s.im ≤ 106
  · by_cases h101 : s.im ≤ 101
    · exact TaoFivePrimes.zeta_zero_free_rectangle_100_101 s hpos h1 him.le h101
    by_cases h102 : s.im ≤ 102
    · exact fun hz => hne (TaoFivePrimes.rh_verified_slice_101_102 s hz hpos h1 (by linarith) h102)
    by_cases h103 : s.im ≤ 103
    · exact TaoFivePrimes.zeta_zero_free_rectangle_102_103 s hpos h1 (by linarith) h103
    by_cases h104 : s.im ≤ 104
    · exact fun hz => hne (TaoFivePrimes.rh_verified_slice_103_104 s hz hpos h1 (by linarith) h104)
    by_cases h105 : s.im ≤ 105
    · exact TaoFivePrimes.zeta_zero_free_rectangle_104_105 s hpos h1 (by linarith) h105
    · exact fun hz => hne (TaoFivePrimes.rh_verified_slice_105_106 s hz hpos h1 (by linarith) h106)
  · exact zeta_ne_zero_of_strip_of_hundred_six_lt_im s h0 h1 (lt_of_not_ge h106)

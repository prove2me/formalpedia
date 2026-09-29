-- Prove2me | solution 2 for zeta_ne_zero_of_strip_of_two_lt_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T11:02:13.629802+00:00
-- url     : https://prove2.me/submissions/5ad53935-8abe-4a8a-b588-99b61c35a33e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_five
import Theorems.Thm_zeta_ne_zero_of_strip_of_five_lt_im

open Complex

theorem solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 2 < s.im) : riemannZeta s ≠ 0 := by
  by_cases hfive : s.im ≤ 5
  · apply zeta_ne_zero_of_mem_strip_of_abs_im_le_five s (by linarith) h1
    rw [abs_of_nonneg (by linarith)]
    exact hfive
  · exact zeta_ne_zero_of_strip_of_five_lt_im s h0 h1 (by linarith)

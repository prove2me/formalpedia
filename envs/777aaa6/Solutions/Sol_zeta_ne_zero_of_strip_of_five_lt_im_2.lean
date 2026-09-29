-- Prove2me | solution 2 for zeta_ne_zero_of_strip_of_five_lt_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T11:03:36.19225+00:00
-- url     : https://prove2.me/submissions/2c96122c-134e-4a29-aa7f-08929e1ff620
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_six
import Theorems.Thm_zeta_ne_zero_of_strip_of_six_lt_im

open Complex

theorem solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 5 < s.im) : riemannZeta s ≠ 0 := by
  by_cases hsix : s.im ≤ 6
  · apply zeta_ne_zero_of_mem_strip_of_abs_im_le_six s (by linarith) h1
    rw [abs_of_nonneg (by linarith)]
    exact hsix
  · exact zeta_ne_zero_of_strip_of_six_lt_im s h0 h1 (by linarith)

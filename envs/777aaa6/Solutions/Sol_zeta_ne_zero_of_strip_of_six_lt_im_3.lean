-- Prove2me | solution 3 for zeta_ne_zero_of_strip_of_six_lt_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T09:17:08.089601+00:00
-- url     : https://prove2.me/submissions/1ed91ccd-f50c-47e7-8a16-8fc8ace5ff02
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_fourteen
import Theorems.Thm_zeta_ne_zero_of_strip_of_fourteen_lt_im

open Complex

theorem solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 6 < s.im) : riemannZeta s ≠ 0 := by
  by_cases h : s.im ≤ 14
  · exact zeta_ne_zero_of_mem_strip_of_abs_im_le_fourteen s (by linarith) h1
      (abs_le.2 ⟨by linarith, h⟩)
  · exact zeta_ne_zero_of_strip_of_fourteen_lt_im s h0 h1 (lt_of_not_ge h)

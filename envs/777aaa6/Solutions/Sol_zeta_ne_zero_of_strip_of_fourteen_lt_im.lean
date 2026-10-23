-- Prove2me | solution 1 for zeta_ne_zero_of_strip_of_fourteen_lt_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T10:04:29.021576+00:00
-- url     : https://prove2.me/submissions/7b3e490d-84b3-44de-8f2b-049fa89206d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_zeta_ne_zero_of_strip_of_fourteen_lt_im_of_im_le_hundred
import Theorems.Thm_zeta_ne_zero_of_strip_of_hundred_lt_im

open Complex

theorem solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 14 < s.im) : riemannZeta s ≠ 0 := by
  by_cases h : s.im ≤ 100
  · exact zeta_ne_zero_of_strip_of_fourteen_lt_im_of_im_le_hundred s h0 h1 him h
  · exact zeta_ne_zero_of_strip_of_hundred_lt_im s h0 h1 (lt_of_not_ge h)

-- Prove2me | solution 1 for zeta_ne_zero_of_half_lt_re
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T12:19:00.998898+00:00
-- url     : https://prove2.me/submissions/bdcffda4-282a-4abc-8c78-426408afc130
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_two
import Theorems.Thm_zeta_ne_zero_of_strip_of_two_lt_abs_im
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

theorem solution (s : ℂ) (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  by_cases h : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h
  · push_neg at h
    by_cases h2 : |s.im| ≤ 2
    · exact zeta_ne_zero_of_mem_strip_of_abs_im_le_two s (by linarith) h h2
    · push_neg at h2
      exact zeta_ne_zero_of_strip_of_two_lt_abs_im s hs h h2

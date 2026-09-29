-- Prove2me | solution 2 for zeta_ne_zero_of_half_lt_re
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:41:56.639337+00:00
-- url     : https://prove2.me/submissions/bd092cf7-db53-4a80-b896-4a06e1420fc9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_zeta_ne_zero_of_strip_of_two_lt_abs_im
import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_two

open Complex

theorem _root_.solution (s : ℂ) (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · push_neg at h1
    by_cases him : |s.im| ≤ 2
    · exact zeta_ne_zero_of_mem_strip_of_abs_im_le_two s (by linarith) h1 him
    · push_neg at him
      exact zeta_ne_zero_of_strip_of_two_lt_abs_im s hs h1 him

#print axioms solution

-- Prove2me | solution 3 for zeta_ne_zero_of_strip_of_five_lt_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:43:11.72031+00:00
-- url     : https://prove2.me/submissions/bab004fd-a386-4a51-9e15-53226359da0e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_zeta_ne_zero_of_strip_of_two_lt_im

theorem _root_.solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 5 < s.im) : riemannZeta s ≠ 0 :=
  zeta_ne_zero_of_strip_of_two_lt_im s h0 h1 (by linarith)

#print axioms solution

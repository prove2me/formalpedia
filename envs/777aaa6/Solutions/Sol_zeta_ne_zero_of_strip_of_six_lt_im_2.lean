-- Prove2me | solution 2 for zeta_ne_zero_of_strip_of_six_lt_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:44:14.74806+00:00
-- url     : https://prove2.me/submissions/50f94094-b040-4e8a-90af-861113e286ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_zeta_ne_zero_of_strip_of_five_lt_im

theorem _root_.solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 6 < s.im) : riemannZeta s ≠ 0 :=
  zeta_ne_zero_of_strip_of_five_lt_im s h0 h1 (by linarith)

#print axioms solution

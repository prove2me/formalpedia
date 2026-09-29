-- Prove2me | solution 3 for zeta_ne_zero_of_strip_of_two_lt_abs_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:49:32.548953+00:00
-- url     : https://prove2.me/submissions/63ba5b48-4d82-4068-9c25-7a87f12d2ff8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_zeta_ne_zero_of_strip_of_two_lt_im
import Theorems.Thm_riemannZeta_conj

open Complex

theorem _root_.solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 2 < |s.im|) : riemannZeta s ≠ 0 := by
  rcases lt_abs.mp him with h | h
  · exact zeta_ne_zero_of_strip_of_two_lt_im s h0 h1 h
  · intro hz
    have hc : riemannZeta ((starRingEnd ℂ) s) = 0 := by
      rw [riemannZeta_conj, hz, map_zero]
    refine zeta_ne_zero_of_strip_of_two_lt_im ((starRingEnd ℂ) s) ?_ ?_ ?_ hc
    · simpa using h0
    · simpa using h1
    · simpa using h

#print axioms solution

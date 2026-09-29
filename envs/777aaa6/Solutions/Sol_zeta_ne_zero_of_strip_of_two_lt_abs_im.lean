-- Prove2me | solution 1 for zeta_ne_zero_of_strip_of_two_lt_abs_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T12:38:43.566857+00:00
-- url     : https://prove2.me/submissions/e5bfe37c-a674-4e0c-b580-2a46dff0da80
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemannZeta_conj
import Theorems.Thm_zeta_ne_zero_of_strip_of_two_lt_im
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

open Complex

theorem solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1) (him : 2 < |s.im|) :
    riemannZeta s ≠ 0 := by
  by_cases hpos : 0 ≤ s.im
  · rw [abs_of_nonneg hpos] at him
    exact zeta_ne_zero_of_strip_of_two_lt_im s h0 h1 him
  · push_neg at hpos
    rw [abs_of_neg hpos] at him
    have hc : riemannZeta ((starRingEnd ℂ) s) ≠ 0 := by
      refine zeta_ne_zero_of_strip_of_two_lt_im _ ?_ ?_ ?_ <;>
        simp only [Complex.conj_re, Complex.conj_im] <;> linarith
    intro hz
    exact hc (by rw [riemannZeta_conj, hz, map_zero])

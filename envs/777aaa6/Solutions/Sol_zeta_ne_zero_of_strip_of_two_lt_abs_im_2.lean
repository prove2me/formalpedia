-- Prove2me | solution 2 for zeta_ne_zero_of_strip_of_two_lt_abs_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T10:58:18.884523+00:00
-- url     : https://prove2.me/submissions/04f2949d-8359-4406-8aae-9fd0e28765e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_zeta_ne_zero_of_strip_of_two_lt_im
import Theorems.Thm_riemannZeta_conj

open Complex

theorem solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 2 < |s.im|) : riemannZeta s ≠ 0 := by
  rcases le_total 0 s.im with hnonneg | hnonpos
  · exact zeta_ne_zero_of_strip_of_two_lt_im s h0 h1 (by
      simpa [abs_of_nonneg hnonneg] using him)
  · have hconj : riemannZeta ((starRingEnd ℂ) s) ≠ 0 :=
      zeta_ne_zero_of_strip_of_two_lt_im ((starRingEnd ℂ) s) (by simpa using h0)
        (by simpa using h1) (by
          simpa [abs_of_nonpos hnonpos] using him)
    intro hz
    apply hconj
    rw [riemannZeta_conj, hz]
    simp

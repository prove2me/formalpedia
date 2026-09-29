-- Prove2me | solution 1 for zeta_ne_zero_of_strip_of_two_lt_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T13:25:31.910995+00:00
-- url     : https://prove2.me/submissions/72e2b5cd-794e-458f-a373-dab8007652b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_five
import Theorems.Thm_zeta_ne_zero_of_strip_of_five_lt_im

open Complex

/-- Reduction of the region `1/2 < Re s < 1`, `Im s > 2` to `Im s > 5`, using the
unconditional zero-free rectangle of height `5`. -/
theorem solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1) (him : 2 < s.im) :
    riemannZeta s ≠ 0 := by
  rcases le_or_gt s.im 5 with h | h
  · exact zeta_ne_zero_of_mem_strip_of_abs_im_le_five s (by linarith) h1
      (abs_le.mpr ⟨by linarith, h⟩)
  · exact zeta_ne_zero_of_strip_of_five_lt_im s h0 h1 h

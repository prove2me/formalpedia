-- Prove2me | solution 1 for zeta_ne_zero_of_strip_of_five_lt_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T13:56:51.662723+00:00
-- url     : https://prove2.me/submissions/e5c1f9e5-0f74-4505-bdfb-24154e92e379
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_six
import Theorems.Thm_zeta_ne_zero_of_strip_of_six_lt_im

open Complex

/-- Reduction of the region `1/2 < Re s < 1`, `Im s > 5` to `Im s > 6`, using the
unconditional zero-free rectangle of height `6`. -/
theorem solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1) (him : 5 < s.im) :
    riemannZeta s ≠ 0 := by
  rcases le_or_gt s.im 6 with h | h
  · exact zeta_ne_zero_of_mem_strip_of_abs_im_le_six s (by linarith) h1
      (abs_le.mpr ⟨by linarith, h⟩)
  · exact zeta_ne_zero_of_strip_of_six_lt_im s h0 h1 h

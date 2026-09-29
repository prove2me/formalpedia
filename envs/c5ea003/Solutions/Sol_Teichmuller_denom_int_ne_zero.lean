-- Prove2me | solution 1 for Teichmuller.denom_int_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T19:36:25.359101+00:00
-- url     : https://prove2.me/submissions/c11e9f76-d60d-4f8c-9b46-646aa17c0e79

import Mathlib
open Complex UpperHalfPlane Matrix MatrixGroups Filter in
theorem solution (g : SL(2, ℤ)) (w : ℍ) :
    ((g 1 0 : ℤ) : ℂ) * (w : ℂ) + ((g 1 1 : ℤ) : ℂ) ≠ 0 := by
  intro h
  -- imaginary part: `c · Im w = 0`, and `Im w > 0`, so `c = 0`
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero, Complex.zero_im] at him
  have hw : 0 < (w : ℂ).im := w.im_pos
  have hc : (g 1 0 : ℤ) = 0 := by
    have : ((g 1 0 : ℤ) : ℝ) = 0 := by
      rcases mul_eq_zero.mp him with h0 | h0
      · exact h0
      · exact absurd h0 (ne_of_gt hw)
    exact_mod_cast this
  -- real part: then `d = 0`, contradicting `ad - bc = 1`
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, hc,
    Int.cast_zero, zero_mul, sub_zero, zero_add, Complex.zero_re] at hre
  have hd : (g 1 1 : ℤ) = 0 := by exact_mod_cast hre
  have hdet := g.det_coe
  rw [Matrix.det_fin_two, hc, hd] at hdet
  simp at hdet

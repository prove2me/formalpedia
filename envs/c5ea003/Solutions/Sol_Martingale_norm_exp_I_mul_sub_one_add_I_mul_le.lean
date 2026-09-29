-- Prove2me | solution 1 for Martingale.norm_exp_I_mul_sub_one_add_I_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T19:01:48.345989+00:00
-- url     : https://prove2.me/submissions/5cdbafd8-6610-4b37-ae8f-94ee8bd13b3c

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

theorem solution (x : ℝ) (hx : |x| ≤ 1) :
    ‖Complex.exp (Complex.I * x) - (1 + Complex.I * x)‖ ≤ x ^ 2 := by
  have hnorm : ‖(Complex.I * (x : ℂ))‖ = |x| := by
    simp [Complex.norm_real]
  have h := Complex.norm_exp_sub_one_sub_id_le (x := Complex.I * (x : ℂ)) (by rw [hnorm]; exact hx)
  calc ‖Complex.exp (Complex.I * x) - (1 + Complex.I * x)‖
      = ‖Complex.exp (Complex.I * (x:ℂ)) - 1 - Complex.I * (x:ℂ)‖ := by ring_nf
    _ ≤ ‖Complex.I * (x : ℂ)‖ ^ 2 := h
    _ = x ^ 2 := by rw [hnorm, sq_abs]

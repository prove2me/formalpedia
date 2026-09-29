-- Prove2me | solution 1 for Martingale.norm_exp_div_one_add_I_mul_le_one
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T19:07:52.976912+00:00
-- url     : https://prove2.me/submissions/c657384e-a590-40cc-ad9b-939de7f951ef

import Mathlib.Analysis.SpecialFunctions.Complex.Circle

theorem solution (θ z : ℝ) :
    ‖Complex.exp (Complex.I * θ * (z : ℂ)) / (1 + Complex.I * θ * (z : ℂ))‖ ≤ 1 := by
  have hden : (1:ℝ) ≤ ‖(1 : ℂ) + Complex.I * θ * (z : ℂ)‖ := by
    have hsq : ‖(1 : ℂ) + Complex.I * θ * (z : ℂ)‖ ^ 2 = 1 + θ ^ 2 * z ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      ring
    nlinarith [norm_nonneg ((1 : ℂ) + Complex.I * θ * (z : ℂ)), sq_nonneg θ, sq_nonneg z,
      mul_nonneg (sq_nonneg θ) (sq_nonneg z)]
  have hnum : ‖Complex.exp (Complex.I * θ * (z : ℂ))‖ = 1 := by
    have : Complex.I * (θ : ℂ) * (z : ℂ) = ((θ * z : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [norm_div, hnum]
  rw [div_le_one (by linarith)]
  exact hden

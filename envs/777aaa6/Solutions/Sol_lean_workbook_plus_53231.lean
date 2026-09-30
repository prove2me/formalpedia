-- Prove2me | solution 1 for lean_workbook_plus_53231
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:25:50.026306+00:00
-- url     : https://prove2.me/submissions/138b8c23-1e84-4b3e-95b1-2cbb4bc5cd9c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem complex_real_sub_imag_norm_sq (x y : ℝ) :
    ‖(x : ℂ) - (y : ℂ) * Complex.I‖ ^ 2 = x ^ 2 + y ^ 2 := by
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem solution (z : ℂ)
    (h : z = (3 + 4 * Complex.I) * (Real.sqrt 2 - Real.sqrt 2 * Complex.I) /
      ((Real.sqrt 3 - Complex.I) * Real.sqrt 5 * Complex.I)) :
    ‖z‖ = Real.sqrt 5 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by positivity)
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by positivity)
  have hp5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by positivity)
  have hn1 : ‖(3 : ℂ) + 4 * Complex.I‖ = 5 := by
    have he := complex_real_sub_imag_norm_sq 3 (-4)
    simp only [Complex.ofReal_ofNat, Complex.ofReal_neg, neg_mul, sub_neg_eq_add] at he
    nlinarith [norm_nonneg ((3 : ℂ) + 4 * Complex.I)]
  have hn2 : ‖(Real.sqrt 2 : ℂ) - Real.sqrt 2 * Complex.I‖ = 2 := by
    have he := complex_real_sub_imag_norm_sq (Real.sqrt 2) (Real.sqrt 2)
    nlinarith [norm_nonneg ((Real.sqrt 2 : ℂ) - Real.sqrt 2 * Complex.I)]
  have hn3 : ‖(Real.sqrt 3 : ℂ) - Complex.I‖ = 2 := by
    have he := complex_real_sub_imag_norm_sq (Real.sqrt 3) 1
    simp only [Complex.ofReal_one, one_mul] at he
    nlinarith [norm_nonneg ((Real.sqrt 3 : ℂ) - Complex.I)]
  rw [h, norm_div, norm_mul, norm_mul, norm_mul, hn1, hn2, hn3,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp5, Complex.norm_I]
  field_simp [hp5.ne']
  nlinarith

#print axioms complex_real_sub_imag_norm_sq
#print axioms solution

-- Prove2me | solution 1 for lean_workbook_plus_29780
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:21:24.627405+00:00
-- url     : https://prove2.me/submissions/72d82f32-84cd-462d-a9f4-6ae7987700d5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem complex_quadratic_norm_difference (z : ℂ) :
    ‖1 + z + z ^ 2‖ ^ 2 - ‖1 + z ^ 2‖ ^ 2 =
      (2 * z.re + 1) * ‖z‖ ^ 2 + 2 * z.re := by
  simp only [Complex.sq_norm]
  simp [Complex.normSq_apply, pow_succ,
    Complex.mul_re, Complex.mul_im]
  ring

theorem complex_quadratic_norm_comparison_iff (z : ℂ) :
    ‖1 + z + z ^ 2‖ < ‖1 + z ^ 2‖ ↔
      (2 * z.re + 1) * ‖z‖ ^ 2 + 2 * z.re < 0 := by
  have hd := complex_quadratic_norm_difference z
  constructor
  · intro h
    nlinarith [norm_nonneg (1 + z + z ^ 2), norm_nonneg (1 + z ^ 2)]
  · intro h
    nlinarith [norm_nonneg (1 + z + z ^ 2), norm_nonneg (1 + z ^ 2)]

theorem solution (z : ℂ) (h : z.re < -1 / 2) :
    ‖1 + z ^ 2‖ > ‖1 + z + z ^ 2‖ := by
  apply (complex_quadratic_norm_comparison_iff z).mpr
  have hx : 2 * z.re + 1 ≤ 0 := by linarith
  have hp := mul_nonpos_of_nonpos_of_nonneg hx (sq_nonneg ‖z‖)
  linarith

#print axioms complex_quadratic_norm_difference
#print axioms complex_quadratic_norm_comparison_iff
#print axioms solution

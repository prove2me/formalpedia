-- Prove2me | solution 1 for lean_workbook_plus_41089
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:25:36.891104+00:00
-- url     : https://prove2.me/submissions/f533b704-34d5-4625-aede-158205dec444

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem complex_real_centers_sq_difference (z : ℂ) (a b : ℝ) :
    ‖z - (b : ℂ)‖ ^ 2 - ‖z - (a : ℂ)‖ ^ 2 =
      (a - b) * (2 * z.re - a - b) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  ring

theorem complex_real_centers_strict_iff (z : ℂ) (a b : ℝ) :
    ‖z - (a : ℂ)‖ < ‖z - (b : ℂ)‖ ↔
      0 < (a - b) * (2 * z.re - a - b) := by
  have hd := complex_real_centers_sq_difference z a b
  constructor <;> intro h <;>
    nlinarith [norm_nonneg (z - (a : ℂ)), norm_nonneg (z - (b : ℂ))]

theorem complex_real_centers_equidistant_iff (z : ℂ) (a b : ℝ) (hab : a ≠ b) :
    ‖z - (a : ℂ)‖ = ‖z - (b : ℂ)‖ ↔ z.re = (a + b) / 2 := by
  have hd := complex_real_centers_sq_difference z a b
  constructor
  · intro h
    have hp : (a - b) * (2 * z.re - a - b) = 0 := by rw [h] at hd; linarith
    have hh := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hab)
    linarith
  · intro h
    have hp : (a - b) * (2 * z.re - a - b) = 0 := by
      have hh : 2 * z.re - a - b = 0 := by linarith
      rw [hh, mul_zero]
    nlinarith [norm_nonneg (z - (a : ℂ)), norm_nonneg (z - (b : ℂ))]

theorem solution (z : ℂ) (h : ‖z - 1‖ < ‖z + 3‖) : z.re > -1 := by
  have hp := (complex_real_centers_strict_iff z 1 (-3)).mp (by simpa using h)
  linarith

#print axioms complex_real_centers_sq_difference
#print axioms complex_real_centers_strict_iff
#print axioms complex_real_centers_equidistant_iff
#print axioms solution

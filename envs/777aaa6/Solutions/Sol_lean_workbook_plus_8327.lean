-- Prove2me | solution 1 for lean_workbook_plus_8327
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:42:44.424226+00:00
-- url     : https://prove2.me/submissions/96ec54c0-3fec-4719-be39-51a83842556c

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (h : (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 = 0) : x = 1 ∧ y = 1 ∧ z = 1 := by
  have hx : (x - 1) ^ 2 = 0 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  have hy : (y - 1) ^ 2 = 0 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  have hz : (z - 1) ^ 2 = 0 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  refine ⟨?_, ?_, ?_⟩
  · have := pow_eq_zero_iff (two_ne_zero) |>.mp hx; linarith
  · have := pow_eq_zero_iff (two_ne_zero) |>.mp hy; linarith
  · have := pow_eq_zero_iff (two_ne_zero) |>.mp hz; linarith

-- Prove2me | solution 1 for lean_workbook_plus_19865
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:39:39.281191+00:00
-- url     : https://prove2.me/submissions/c89eb193-da51-4118-a1e8-b66cd7cdca6d

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (h : x^3 + y^3 + z^3 = 3 * x * y * z) :  x + y + z = 0 ∨ x = y ∧ y = z := by
  have key : (x + y + z) * ((x - y)^2 + (y - z)^2 + (z - x)^2) = 0 := by
    nlinarith [h]
  rcases mul_eq_zero.mp key with h1 | h2
  · left; exact h1
  · right
    have hx : (x - y)^2 = 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    have hy : (y - z)^2 = 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    constructor
    · nlinarith [pow_eq_zero_iff (n := 2) (a := x - y) (by norm_num) |>.mp hx]
    · nlinarith [pow_eq_zero_iff (n := 2) (a := y - z) (by norm_num) |>.mp hy]

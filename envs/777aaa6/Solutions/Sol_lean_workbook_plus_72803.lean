-- Prove2me | solution 1 for lean_workbook_plus_72803
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:05:28.994842+00:00
-- url     : https://prove2.me/submissions/9c037c8f-4b47-49a8-b0eb-7e551ca1c77a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x > 0) (hy : y > 0) : x^4 + y^4 + x^2 + y^2 + 2 + 2 * x * (4 * x^2 + 1) + 2 * y * (4 * y^2 + 1) > 18 * x * y   := by
  have hA : 0 ≤ y * (1 - 2 * y) ^ 2 := by positivity
  have hB : 0 < x * (1 + 2 * x) ^ 2 := by positivity
  have hC : 0 ≤ x * (1 - 2 * x) ^ 2 := by positivity
  nlinarith [sq_nonneg (1 - x * y), sq_nonneg (x - y), sq_nonneg (x - 2 * y), sq_nonneg (x ^ 2 - y ^ 2)]

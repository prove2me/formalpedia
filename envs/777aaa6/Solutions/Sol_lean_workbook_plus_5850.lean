-- Prove2me | solution 1 for lean_workbook_plus_5850
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:44:41.806519+00:00
-- url     : https://prove2.me/submissions/99b0c99e-3bcd-42a4-98af-846f1bd75c87

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d e : ℝ) (h : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0 ∨ e = 0) : b^4 + c^4 + d^4 + e^4 ≥ 4 * b * c * d * e := by
  nlinarith [sq_nonneg (b^2 - c^2), sq_nonneg (d^2 - e^2), sq_nonneg (b*c - d*e), sq_nonneg (b*c + d*e)]

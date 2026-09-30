-- Prove2me | solution 1 for lean_workbook_plus_57696
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:04:14.026315+00:00
-- url     : https://prove2.me/submissions/f3e29c0b-2fb0-435e-a3fc-89d4fe2fcb86

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (x y : ℝ) : x^4+y^4+8 ≥ 8*x*y := by
  nlinarith [sq_nonneg (x^2 - 2), sq_nonneg (y^2 - 2), sq_nonneg (x - y)]

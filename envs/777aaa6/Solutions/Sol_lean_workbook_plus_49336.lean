-- Prove2me | solution 1 for lean_workbook_plus_49336
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:09:44.780674+00:00
-- url     : https://prove2.me/submissions/91777948-f5c6-4dee-8788-298012b88da6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (hab : a^2 * b^2 + a + b = 7 * a * b) : a * b + a + b ≤ 16 := by
  nlinarith [sq_nonneg (a*b-4)]

-- Prove2me | solution 1 for lean_workbook_plus_6373
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:40:16.256876+00:00
-- url     : https://prove2.me/submissions/26410a88-0b41-4c22-a095-a453a2d6bf06

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b : ℝ) : (a^4 + 1) * (1 + b^4) ≥ (a^2 + b^2)^2 := by
  nlinarith [sq_nonneg (a ^ 2 * b ^ 2 - 1)]

-- Prove2me | solution 1 for lean_workbook_plus_69718
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:40:14.946813+00:00
-- url     : https://prove2.me/submissions/7f27e318-ad28-4edf-9cbe-0bc63d619c47

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b: ℝ) : (a + b) ^ 2 ≥ 4 * a * b := by
  nlinarith [sq_nonneg (a - b)]

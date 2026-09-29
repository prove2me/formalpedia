-- Prove2me | solution 1 for lean_workbook_plus_6000
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:40:21.439676+00:00
-- url     : https://prove2.me/submissions/28a2e0d4-38ca-41af-834c-48c7b99812a1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (x : ℝ) : x ^ 8 - x ^ 5 + x ^ 2 - x + 1 > 0 := by
  nlinarith only [sq_nonneg (2 * x ^ 4 - x), sq_nonneg (3 * x - 2)]

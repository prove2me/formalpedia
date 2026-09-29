-- Prove2me | solution 1 for lean_workbook_plus_68769
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:40:15.621532+00:00
-- url     : https://prove2.me/submissions/f6bd24ee-612f-4e67-82af-fb39be1c1c0c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a c : ℝ) : 25 * a ^ 2 + 25 * c ^ 2 - 34 * a * c ≥ 0 := by
  nlinarith [sq_nonneg (a - c), sq_nonneg (a + c)]

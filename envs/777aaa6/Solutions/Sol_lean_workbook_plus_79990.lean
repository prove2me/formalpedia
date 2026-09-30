-- Prove2me | solution 1 for lean_workbook_plus_79990
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:17:30.734742+00:00
-- url     : https://prove2.me/submissions/ef28aa9b-6272-4c64-8d35-fa1d0e48aaeb

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a : ℝ) : a ^ 6 + a ^ 4 - a ^ 3 - a + 1 ≥ 1 / 4 := by
  nlinarith [sq_nonneg (a ^ 3 - 1 / 2), sq_nonneg (a ^ 2 - 1 / 2),
    sq_nonneg (a - 1 / 2)]

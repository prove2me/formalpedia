-- Prove2me | solution 1 for lean_workbook_plus_64577
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:02:32.971273+00:00
-- url     : https://prove2.me/submissions/e3672fa3-2ea0-4aed-bf38-fd1a16c5dfce

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 2 ≠ 0 ∧ 3 ≠ 0 ∧ 4 ≠ 0 ∧ 5 ≠ 0 ∧ 6 ≠ 0 ∧ 7 ≠ 0 ∧ 8 ≠ 0 ∧ 9 ≠ 0 ∧ 10 ≠ 0) : (1 / 2 * 2 / 3 * 3 / 4 * 4 / 5 * 5 / 6 * 6 / 7 * 7 / 8 * 8 / 9 * 9 / 10) = 1 / 10 := by
  norm_num

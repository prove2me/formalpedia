-- Prove2me | solution 1 for lean_workbook_plus_55066
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:21.992106+00:00
-- url     : https://prove2.me/submissions/eead22f3-31db-4aa1-8518-03cc005664ba

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (hn : n ≠ 0) : (1 : ℝ) / (n * (n + 1) * (n + 2) * (n + 3)) = 1 / (6 * n) - 1 / (6 * (n + 3)) - 1 / (2 * (n + 1)) + 1 / (2 * (n + 2)) := by
  (intros; field_simp; ring)

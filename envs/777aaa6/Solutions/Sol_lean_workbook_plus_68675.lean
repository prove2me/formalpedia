-- Prove2me | solution 1 for lean_workbook_plus_68675
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-04-15T02:19:15.111667+00:00
-- url     : https://prove2.me/submissions/7e0da394-b7f2-4040-92c3-7701e964b1be

import Theorems.Thm_lean_workbook_plus_68675

theorem solution : ∀ x : ℝ, x ^ 2 + 2 * x + 3 ≥ 0 := by
  intro x
  nlinarith [sq_nonneg (x + 1)]

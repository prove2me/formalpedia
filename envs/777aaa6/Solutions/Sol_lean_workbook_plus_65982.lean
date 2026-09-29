-- Prove2me | solution 1 for lean_workbook_plus_65982
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:25.090289+00:00
-- url     : https://prove2.me/submissions/a0ed4b09-ba97-41ae-8741-779352fe3409

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℝ) (r : ℝ) : 3 * (p / 3 - 3 * r) + 9 * r ≥ p := by
  (intros; linarith)

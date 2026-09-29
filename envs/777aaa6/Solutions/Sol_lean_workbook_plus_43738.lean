-- Prove2me | solution 1 for lean_workbook_plus_43738
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:00.898136+00:00
-- url     : https://prove2.me/submissions/5b8841fe-2d2e-4e17-a47c-b88ccc768802

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (s p : ℝ) : 9/5 * s - 16/5 * p = 0 → s = 16/9 * p := by
  (intros; linarith)

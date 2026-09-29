-- Prove2me | solution 1 for lean_workbook_plus_76123
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:18:49.738109+00:00
-- url     : https://prove2.me/submissions/cf1e76fa-6111-4bde-92bc-22c654a7e717

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : x^2 + 200 * x + 1 < (x + 100)^2 := by
  (intros; linarith)

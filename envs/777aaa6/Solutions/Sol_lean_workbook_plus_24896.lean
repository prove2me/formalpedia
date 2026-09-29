-- Prove2me | solution 1 for lean_workbook_plus_24896
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:07.231851+00:00
-- url     : https://prove2.me/submissions/84fe7364-b4a4-42b6-be47-9b6f882c3980

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (h : 2 * (2 * x + 1) = 2 * 8) : 4 * x + 2 = 16 := by
  (intros; linarith)

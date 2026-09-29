-- Prove2me | solution 1 for lean_workbook_plus_48087
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:50:22.860887+00:00
-- url     : https://prove2.me/submissions/59f495fc-fe57-4f52-81ed-27563856f9af

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : a / (b + c) + b / (a + c) + c / (a + b) = (a / (b + c) + 1 + b / (a + c) + 1 + c / (a + b) + 1) - 3 := by
  (intros; linarith)

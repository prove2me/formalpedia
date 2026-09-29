-- Prove2me | solution 1 for lean_workbook_plus_78031
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:24:40.992578+00:00
-- url     : https://prove2.me/submissions/3b074af5-7674-42a1-a40a-d8b52a00df51

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k : ℝ) : k^2 - (k + 1)^2 - (k + 2)^2 + (k + 3)^2 = 4 := by
  (intros; linarith)

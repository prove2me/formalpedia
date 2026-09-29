-- Prove2me | solution 1 for lean_workbook_plus_10457
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:31.952711+00:00
-- url     : https://prove2.me/submissions/046024e7-acff-46ca-ba2f-379f87c26184

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (s : ℝ) : s / 20 - s / 30 = s / 60 := by
  (intros; linarith)

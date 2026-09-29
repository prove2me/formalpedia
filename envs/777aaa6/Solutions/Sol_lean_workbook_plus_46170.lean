-- Prove2me | solution 1 for lean_workbook_plus_46170
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:13.532122+00:00
-- url     : https://prove2.me/submissions/c0a5c8e6-e928-47d4-9e87-b18d52e73cdd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : (30 - x) ^ 2 + 15 ^ 2 = (15 + x) ^ 2) : x = 10 := by
  (intros; linarith)

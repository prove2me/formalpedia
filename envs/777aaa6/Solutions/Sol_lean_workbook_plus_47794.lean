-- Prove2me | solution 1 for lean_workbook_plus_47794
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:04:39.687012+00:00
-- url     : https://prove2.me/submissions/252759a8-61c8-4c41-9950-137bff17b127

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℚ) (h : a = 15 / 24) : a / 60 = 1 / 96 := by
  (intros; linarith)

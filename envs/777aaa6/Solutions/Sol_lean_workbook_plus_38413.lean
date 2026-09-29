-- Prove2me | solution 1 for lean_workbook_plus_38413
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:07.544886+00:00
-- url     : https://prove2.me/submissions/9ebdfd1a-0916-49ee-b6d5-888034e8f809

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (h : 4 - x / 2013 = x / 671) : x = 2013 := by
  (intros; linarith)

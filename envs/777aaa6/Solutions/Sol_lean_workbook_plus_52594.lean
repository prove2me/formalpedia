-- Prove2me | solution 1 for lean_workbook_plus_52594
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:16.845447+00:00
-- url     : https://prove2.me/submissions/396cf668-1300-45d5-925f-ee8a842dd9c1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : (a + b) / 2 = 12) : a + b = 24 := by
  (intros; linarith)

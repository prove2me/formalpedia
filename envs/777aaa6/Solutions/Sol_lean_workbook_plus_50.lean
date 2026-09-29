-- Prove2me | solution 1 for lean_workbook_plus_50
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:30.4884+00:00
-- url     : https://prove2.me/submissions/4b22adef-4c8f-42fc-95a2-4a3452980723

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℝ)
  (h₀ : p = 0.5 / 5.5) :
  p = 1 / 11 := by
  (intros; linarith)

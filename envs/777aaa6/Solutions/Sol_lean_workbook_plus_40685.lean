-- Prove2me | solution 1 for lean_workbook_plus_40685
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:39:59.914206+00:00
-- url     : https://prove2.me/submissions/cae39581-61d6-46b0-9d1c-1ac0fa82acc3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a p : ℝ) (h₁ : a = 2 - p) (h₂ : 9 = 2 + p) : a = -5 := by
  (intros; linarith)

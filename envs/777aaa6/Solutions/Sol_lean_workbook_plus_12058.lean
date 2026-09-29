-- Prove2me | solution 1 for lean_workbook_plus_12058
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:26.155505+00:00
-- url     : https://prove2.me/submissions/18e010a7-cf61-4ff8-80de-4f48b10fe79b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) : ∀ x, f x = (f x + f (-x)) / 2 + (f x - f (-x)) / 2 := by
  (intros; linarith)

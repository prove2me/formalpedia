-- Prove2me | solution 1 for lean_workbook_plus_64743
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:14.350893+00:00
-- url     : https://prove2.me/submissions/d7abb2c4-ef58-4755-a498-b9730ab2990f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ)
  (h₀ : a / 4 = 1) :
  a = 4 := by
  (intros; linarith)

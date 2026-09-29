-- Prove2me | solution 1 for lean_workbook_plus_58897
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:15.634523+00:00
-- url     : https://prove2.me/submissions/00003951-a5f2-4963-a650-7cbd39f616d9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a - b = 1) : a^2 - b^2 = (a + b) * (a - b) := by
  (intros; linarith)

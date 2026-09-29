-- Prove2me | solution 1 for lean_workbook_plus_16617
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:25.299899+00:00
-- url     : https://prove2.me/submissions/6f136944-4c55-4b4b-b5e8-142690731996

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h₁ : d = -a - b - c) :
  a^3 + b^3 + c^3 - (a + b + c)^3 =
    3 * (a * b * c - (a + b + c) * a * b - (a + b + c) * b * c - (a + b + c) * c * a) := by
  (intros; linarith)

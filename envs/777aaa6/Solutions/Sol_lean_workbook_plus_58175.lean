-- Prove2me | solution 1 for lean_workbook_plus_58175
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:21.089957+00:00
-- url     : https://prove2.me/submissions/8712cccb-bd0b-4797-93be-b4924473a729

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a * b + a / 2 - a * b / 2 = 1 / 2) :
  a * (1 + b) = 1 := by
  (intros; linarith)

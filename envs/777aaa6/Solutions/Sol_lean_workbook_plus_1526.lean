-- Prove2me | solution 1 for lean_workbook_plus_1526
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:08.729678+00:00
-- url     : https://prove2.me/submissions/eb5492bc-2665-4e9c-a566-97927340c8d9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a₁ a₂ y : ℝ) : a₂ - a₁ = y → a₂ = y + a₁ := by
  (intros; linarith)

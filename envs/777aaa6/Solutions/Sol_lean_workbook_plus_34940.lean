-- Prove2me | solution 1 for lean_workbook_plus_34940
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:17:39.87237+00:00
-- url     : https://prove2.me/submissions/7738e09a-986e-4c1e-9fd3-97024d37b5cb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :  ∀ a b c : ℝ, (a^4 + b^4 + c^4 + 3 * (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) - 2 * (b * c * (b^2 + c^2) + c * a * (c^2 + a^2) + a * b * (a^2 + b^2))) = (a^2 + b^2 + c^2 - b * c - c * a - a * b)^2 := by
  (intros; linarith)

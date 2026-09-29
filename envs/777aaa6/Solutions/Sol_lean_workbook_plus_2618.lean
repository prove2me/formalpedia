-- Prove2me | solution 1 for lean_workbook_plus_2618
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:53.250479+00:00
-- url     : https://prove2.me/submissions/900a2cfc-2cd1-44a3-9a88-57d5a6217d31

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, (a^2 + b^2 + c^2)^2 ≥ (a * (a - b + c) + b * (b - c + a) + c * (c - a + b))^2 := by
  (intros; linarith)

-- Prove2me | solution 1 for lean_workbook_plus_48782
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:35.772003+00:00
-- url     : https://prove2.me/submissions/c8a5f6d3-2434-4e24-8fa9-2f0697c93a56

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, a^3 + b^3 + c^3 - 3*a*b*c = 1/2 * (a + b + c) * ((a - b)^2 + (b - c)^2 + (c - a)^2) := by
  (intros; linarith)

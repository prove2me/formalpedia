-- Prove2me | solution 1 for lean_workbook_plus_79950
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:00:14.252613+00:00
-- url     : https://prove2.me/submissions/08bb3c39-df7c-4abf-bf02-532b8246de53

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y : ℝ, 12 * (x^3 + 14 * x^2 - 2 * x - (y^3 + 14 * y^2 - 2 * y)) = (x - y) * (3 * (2 * x + y + 14)^2 + (3 * y + 14)^2 - 808) := by
  (intros; linarith)

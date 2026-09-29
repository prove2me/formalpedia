-- Prove2me | solution 1 for lean_workbook_plus_75609
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:53:26.064149+00:00
-- url     : https://prove2.me/submissions/000522b3-9366-4e16-aef2-8289046ab34a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y : ℝ, x^3 + y^3 = (x + y) * (x^2 - x * y + y^2) := by
  (intros; linarith)

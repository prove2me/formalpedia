-- Prove2me | solution 1 for lean_workbook_plus_18375
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:43:41.595323+00:00
-- url     : https://prove2.me/submissions/8a8dc251-7751-4ec5-b06d-6a906d2379e5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c d : ℤ, (a+b+c+d)^2 - 2 * (a * (b + c) + b * (c + d) + c * (d + a) + d * (a + b)) = (b - d)^2 + (a - c)^2 := by
  (intros; linarith)

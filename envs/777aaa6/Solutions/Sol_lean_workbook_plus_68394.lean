-- Prove2me | solution 1 for lean_workbook_plus_68394
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:34.444069+00:00
-- url     : https://prove2.me/submissions/1640864b-051e-4b12-b180-a5ff89109273

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, a^3 + b^3 + c^3 - 3*a*b*c = (a^2 + b^2 + c^2 - a*b - b*c - c*a)*(a + b + c) := by
  (intros; linarith)

-- Prove2me | solution 1 for lean_workbook_plus_68629
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:34.632479+00:00
-- url     : https://prove2.me/submissions/a74f8012-d8a3-4090-a32e-af1018fe8f88

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, (a+b+c)*(a^2+b^2+c^2-a*b-b*c-c*a) - (a+b+c)^3 = -3*(a+b+c)*(a*b+b*c+c*a) := by
  (intros; linarith)

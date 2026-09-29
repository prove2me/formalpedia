-- Prove2me | solution 1 for lean_workbook_plus_41527
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:39:17.462813+00:00
-- url     : https://prove2.me/submissions/50ce5010-8870-497e-ace1-a3e747c383e0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c d : ℝ, (c^2+a^2)*(d^2+b^2)-1/4*(c^2+a^2)*(b+d)^2-1/4*(d^2+b^2)*(c+a)^2 = 1/4*a^2*(b-d)^2+1/4*d^2*(a-c)^2+1/4*c^2*(d-b)^2+1/4*b^2*(c-a)^2 := by
  (intros; linarith)

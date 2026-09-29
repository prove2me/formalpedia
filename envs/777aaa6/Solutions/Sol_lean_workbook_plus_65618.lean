-- Prove2me | solution 1 for lean_workbook_plus_65618
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:32.697306+00:00
-- url     : https://prove2.me/submissions/c7d98222-0355-4557-860f-a93917bed890

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a^4 + 4*a^3*b + 6*a^2*b^2 + 4*a*b^3 + b^4 ≥ 8*a^3*b + 8*a*b^3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])

-- Prove2me | solution 1 for lean_workbook_plus_7211
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:59:08.654769+00:00
-- url     : https://prove2.me/submissions/dbe129a0-79fa-4c20-a4f9-cfdc4d92f665

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a^2+b^2+6*a*b)*(3*a^2+2*a*b+3*b^2) ≤ 4*(a+b)^4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])

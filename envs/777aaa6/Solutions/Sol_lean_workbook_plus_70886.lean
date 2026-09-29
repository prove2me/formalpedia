-- Prove2me | solution 1 for lean_workbook_plus_70886
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:50:58.664963+00:00
-- url     : https://prove2.me/submissions/05efe256-2f55-4bf4-8af2-aa6e107c3fac

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 + b^2 + c^2)^2 ≥ a^2 * (b^2 + b * c + a^2) + b^2 * (c^2 + c * a + b^2) + c^2 * (a^2 + a * b + c^2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

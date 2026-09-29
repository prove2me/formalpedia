-- Prove2me | solution 1 for lean_workbook_plus_72198
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:29.463748+00:00
-- url     : https://prove2.me/submissions/619cd9a4-3f8b-4e51-8349-8faca35b2c05

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^4 + b^4 + c^4 + 3 * (a^2 * b^2 + b^2 * c^2 + a^2 * c^2) ≥ 2 * (a^3 * b + b^3 * a + a^3 * c + c^3 * a + b^3 * c + c^3 * b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

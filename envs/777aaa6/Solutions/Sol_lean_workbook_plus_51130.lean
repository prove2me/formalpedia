-- Prove2me | solution 1 for lean_workbook_plus_51130
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:12.529763+00:00
-- url     : https://prove2.me/submissions/a965d634-eca1-4542-840c-6bd7a03751ff

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 * b^2 - a^2 * b * c + 2 * a^4 + 4 * a^2 * b^2) + (b^2 * c^2 - b^2 * c * a + 2 * b^4 + 4 * b^2 * c^2) + (c^2 * a^2 - c^2 * a * b + 2 * c^4 + 4 * c^2 * a^2) ≥ (2 * a^3 * b + 2 * a^3 * c + 2 * a^2 * b * c) + (2 * b^3 * c + 2 * b^3 * a + 2 * b^2 * c * a) + (2 * c^3 * a + 2 * c^3 * b + 2 * c^2 * a * b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

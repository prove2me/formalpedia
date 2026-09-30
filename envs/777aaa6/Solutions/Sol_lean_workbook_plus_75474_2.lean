-- Prove2me | solution 2 for lean_workbook_plus_75474
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:53:18.925265+00:00
-- url     : https://prove2.me/submissions/d0f277b6-4349-4285-b013-c47e54449e2b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 + b^2 + c^2)^2 - 2 * (a^3 * b + b^3 * c + c^3 * a) ≥ 2 * a * b * c * (a + b + c) - (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

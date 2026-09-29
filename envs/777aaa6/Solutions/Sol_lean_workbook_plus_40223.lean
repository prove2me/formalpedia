-- Prove2me | solution 1 for lean_workbook_plus_40223
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:40:38.381587+00:00
-- url     : https://prove2.me/submissions/0c28e3b2-cd21-45a5-92e1-cd417de38f35

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3 + a * b ^ 2 + b * c ^ 2 + c * a ^ 2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

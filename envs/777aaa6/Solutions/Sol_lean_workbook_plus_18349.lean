-- Prove2me | solution 1 for lean_workbook_plus_18349
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:34.163764+00:00
-- url     : https://prove2.me/submissions/0a138217-ca02-42c9-8765-773c41ed3603

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : a^4 + b^4 + c^4 + 6 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ 2 * (a * b * (a^2 + b^2) + b * c * (b^2 + c^2) + c * a * (c^2 + a^2)) + 3 * a * b * c * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

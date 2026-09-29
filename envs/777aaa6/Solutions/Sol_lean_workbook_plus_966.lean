-- Prove2me | solution 1 for lean_workbook_plus_966
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:50.469582+00:00
-- url     : https://prove2.me/submissions/2b0de395-fc1d-4e48-96da-8d2b2a5b22ec

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (3 / 4) * (a + b) ^ 2 ≥ 3 * a * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])

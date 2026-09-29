-- Prove2me | solution 1 for lean_workbook_plus_35532
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:42:43.768217+00:00
-- url     : https://prove2.me/submissions/5b3779ca-ab58-497d-8262-075cfb574943

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a + 7 * b) * (4 * a + b) ≥ 3 * a ^ 2 + 33 * a * b + 2 * b ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])

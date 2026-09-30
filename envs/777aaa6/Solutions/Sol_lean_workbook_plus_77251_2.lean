-- Prove2me | solution 2 for lean_workbook_plus_77251
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:01:57.69307+00:00
-- url     : https://prove2.me/submissions/f29393e7-3012-4f82-bddb-c1e229b0636d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 6 * (a * b + b * c + c * a) ^ 2 ≥ (a + b + c) ^ 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])

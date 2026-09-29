-- Prove2me | solution 1 for lean_workbook_plus_3917
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:27.157442+00:00
-- url     : https://prove2.me/submissions/9022ce24-69ef-45d9-95ce-4ba201a1fe11

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

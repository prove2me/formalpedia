-- Prove2me | solution 1 for lean_workbook_plus_57277
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:24:19.588274+00:00
-- url     : https://prove2.me/submissions/457b4dee-4450-46a4-9b33-5620dc44e1e2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : 5 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 4 * (x * y + y * z + z * x) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

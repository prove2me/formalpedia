-- Prove2me | solution 1 for lean_workbook_plus_79313
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:18:42.89417+00:00
-- url     : https://prove2.me/submissions/d3ee2b3b-2a8d-4b0f-9111-25613e16b050

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ 1 / 3 * (x + y + z) ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

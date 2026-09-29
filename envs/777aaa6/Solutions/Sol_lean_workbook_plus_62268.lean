-- Prove2me | solution 1 for lean_workbook_plus_62268
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:54.35971+00:00
-- url     : https://prove2.me/submissions/78c043d6-66e6-4802-8a6a-0f6a9afebbd5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x ^ 2 + y ^ 2 + z ^ 2 = 3) : 1 ≥ (x + y + z) / 3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

-- Prove2me | solution 1 for lean_workbook_plus_64649
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:19.521801+00:00
-- url     : https://prove2.me/submissions/1c2ab507-c576-4ce1-91fd-7047b2305ee5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : 3 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ (x + y + z) ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

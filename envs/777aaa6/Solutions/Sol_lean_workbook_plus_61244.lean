-- Prove2me | solution 1 for lean_workbook_plus_61244
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:11.602192+00:00
-- url     : https://prove2.me/submissions/6a3de11e-759d-4db0-ae74-037fe785afa8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 ≥ (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 / 3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

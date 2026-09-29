-- Prove2me | solution 1 for lean_workbook_plus_55154
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:44:36.03019+00:00
-- url     : https://prove2.me/submissions/efc23d88-d0c4-4a2d-a91d-540e5f533960

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y u v : ℝ) (hx : x ^ 2 + y ^ 2 = 1) (hu : u ^ 2 + v ^ 2 = 1) : x * u + y * v ≤ 1 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (u), sq_nonneg (v), sq_nonneg (x - y), sq_nonneg (x - u), sq_nonneg (x - v), sq_nonneg (y - u), sq_nonneg (y - v), sq_nonneg (u - v), sq_nonneg (x + y), sq_nonneg (x + u), sq_nonneg (x + v), sq_nonneg (y + u), sq_nonneg (y + v), sq_nonneg (u + v)])

-- Prove2me | solution 1 for lean_workbook_plus_8132
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:18.510227+00:00
-- url     : https://prove2.me/submissions/86a4f5e8-4e32-46f5-beb9-c40757c86f6b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : x + y + z >= x*y*z → 1/(x*y) + 1/(y*z) + 1/(x*z) >= 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

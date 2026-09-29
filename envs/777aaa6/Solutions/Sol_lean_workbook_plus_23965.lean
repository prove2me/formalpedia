-- Prove2me | solution 1 for lean_workbook_plus_23965
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:16:08.187912+00:00
-- url     : https://prove2.me/submissions/a34711d6-4b1f-4386-9660-ab8061b39b62

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x ≥ -1) (hy : y ≥ -1) (hz : z ≥ -1) (hxy : x + y ≥ 2) (hxz : x + z ≥ 2) (hyz : y + z ≥ 2) : x * y + x * z + y * z ≥ 3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

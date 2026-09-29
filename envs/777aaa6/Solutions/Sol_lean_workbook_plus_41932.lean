-- Prove2me | solution 1 for lean_workbook_plus_41932
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:51.587708+00:00
-- url     : https://prove2.me/submissions/4d9b2321-736a-41b9-9a4a-d7cbd97d519d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y + z ≥ 3) : x * y * z + x ^ 3 + y ^ 3 + z ^ 3 ≥ (4 / 9) * (x + y + z) * (x * y + x * z + y * z) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

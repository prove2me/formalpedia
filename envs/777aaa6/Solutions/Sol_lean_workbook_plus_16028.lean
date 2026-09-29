-- Prove2me | solution 1 for lean_workbook_plus_16028
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:20:52.996615+00:00
-- url     : https://prove2.me/submissions/5c6648e8-2262-4fb6-90b2-743afd891c53

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z: ℝ) (h : x + y + z = 1) : x ^ 2 + y ^ 2 + z ^ 2 ≥ 1 / 3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

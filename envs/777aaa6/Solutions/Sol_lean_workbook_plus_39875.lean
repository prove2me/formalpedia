-- Prove2me | solution 1 for lean_workbook_plus_39875
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:07.784849+00:00
-- url     : https://prove2.me/submissions/4291e3de-0824-4264-8598-51f365fd66bc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x^2 - x * (y + z) + y^2 - y * z + z^2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

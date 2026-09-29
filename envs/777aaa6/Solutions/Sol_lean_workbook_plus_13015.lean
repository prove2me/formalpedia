-- Prove2me | solution 1 for lean_workbook_plus_13015
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:32:18.681149+00:00
-- url     : https://prove2.me/submissions/195d3d84-b9cf-4db8-a26e-6ba2e9ed1212

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

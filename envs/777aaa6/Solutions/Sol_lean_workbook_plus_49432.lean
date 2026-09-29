-- Prove2me | solution 1 for lean_workbook_plus_49432
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:27.695851+00:00
-- url     : https://prove2.me/submissions/5efc55f6-fd99-40eb-94fc-1e8496683f87

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z: ℝ) : x ^ 2 - 2 * x * y + y ^ 2 + y ^ 2 - 2 * y * z + z ^ 2 + x ^ 2 - 2 * x * z + z ^ 2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

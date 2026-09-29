-- Prove2me | solution 1 for lean_workbook_plus_78120
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:25:01.974633+00:00
-- url     : https://prove2.me/submissions/451c7b6c-43ce-483a-8e28-4b3784627fc0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z: ℝ) : 4 * (x + y + z) ^ 2 ≥ 3 * ((x + y + z) ^ 2 + x * y + y * z + z * x) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

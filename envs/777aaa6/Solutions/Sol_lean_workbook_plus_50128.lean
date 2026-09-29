-- Prove2me | solution 1 for lean_workbook_plus_50128
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:21:02.255134+00:00
-- url     : https://prove2.me/submissions/3b61a21b-eebe-4e0b-89df-a20859f76da0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x^2 + y^2 + 12 * z^2 + 1 - 4 * z * (x + y + 1) = (x - 2 * z)^2 + (y - 2 * z)^2 + (2 * z - 1)^2 ∧ (x - 2 * z)^2 + (y - 2 * z)^2 + (2 * z - 1)^2 >= 0 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

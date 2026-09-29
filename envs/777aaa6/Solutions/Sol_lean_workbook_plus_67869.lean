-- Prove2me | solution 1 for lean_workbook_plus_67869
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:26.137211+00:00
-- url     : https://prove2.me/submissions/3d66b13d-95c2-442c-a59d-21ed1d45b68f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y : ℝ) (k : ℝ) (hy : 0 ≤ y ∧ y ≤ 4 * k - 1 / 2) :
  1 / 8 + y / 4 ∈ Set.Icc 0 k := by
  (intros; constructor <;> nlinarith [sq_nonneg (y), sq_nonneg (k), sq_nonneg (y - k), sq_nonneg (y + k)])

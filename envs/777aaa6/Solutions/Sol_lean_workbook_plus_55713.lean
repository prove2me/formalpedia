-- Prove2me | solution 1 for lean_workbook_plus_55713
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:21:46.073462+00:00
-- url     : https://prove2.me/submissions/31651701-6f9c-47ac-be15-6f44f5b28544

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x ∧ 0 < y ∧ 0 < z) (hab : x + y > z) (hbc : y + z > x) (hca : z + x > y) : x ^ 2 + y ^ 2 + z ^ 2 ≤ 2 * x * y + 2 * y * z + 2 * z * x := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

-- Prove2me | solution 1 for lean_workbook_plus_19702
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:38.91241+00:00
-- url     : https://prove2.me/submissions/834140b4-1786-4a7b-af50-ec443014ae43

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x + y + z >= 9 ∧ x * y * z = x ^ 2 + y ^ 2 + z ^ 2) → x ^ 2 + y ^ 2 + z ^ 2 >= (x + y + z) ^ 2 / 3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])

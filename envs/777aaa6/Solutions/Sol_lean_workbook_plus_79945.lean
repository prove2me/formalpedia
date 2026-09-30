-- Prove2me | solution 1 for lean_workbook_plus_79945
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:20:24.012742+00:00
-- url     : https://prove2.me/submissions/3257e4c3-fb14-4107-abd8-43ef1ba242ef

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    1 / (4 + a ^ 2 - 2 * b * c) ≤ 9 / 11 := by
  have hd : 3 ≤ 4 + a ^ 2 - 2 * b * c := by nlinarith [sq_nonneg (b - c)]
  apply (div_le_iff₀ (by linarith : 0 < 4 + a ^ 2 - 2 * b * c)).mpr
  linarith

#print axioms solution

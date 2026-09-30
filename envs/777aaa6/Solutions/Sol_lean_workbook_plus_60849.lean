-- Prove2me | solution 1 for lean_workbook_plus_60849
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:04:36.349436+00:00
-- url     : https://prove2.me/submissions/bc789575-dbe0-44f2-b41f-43119cd9b69d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace PositiveCubicReciprocal

theorem gap_identity (y : ℝ) (hy : y ≠ 0) :
    y * (y ^ 3 + 4 * y + 2 / y - 2 * y ^ 2 - 4) =
      (y ^ 2 - y) ^ 2 + 3 * (y - 2 / 3) ^ 2 + 2 / 3 := by
  field_simp [hy]
  <;> ring

theorem quantitative_bound (y : ℝ) (hy : 0 < y) :
    4 + 2 / (3 * y) ≤ y ^ 3 + 4 * y + 2 / y - 2 * y ^ 2 := by
  apply (mul_le_mul_iff_left₀ hy).mp
  have hid := gap_identity y (ne_of_gt hy)
  have hcancel : y * (2 / (3 * y)) = 2 / 3 := by field_simp [ne_of_gt hy]
  nlinarith [sq_nonneg (y ^ 2 - y), sq_nonneg (y - 2 / 3)]

theorem strict_bound (y : ℝ) (hy : 0 < y) :
    4 < y ^ 3 + 4 * y + 2 / y - 2 * y ^ 2 := by
  have hp : 0 < 2 / (3 * y) := by positivity
  linarith [quantitative_bound y hy]

end PositiveCubicReciprocal

theorem solution (y : ℝ) (hy : y > 0) :
    y ^ 3 + 4 * y + 2 / y - 2 * y ^ 2 ≥ 4 :=
  le_of_lt (PositiveCubicReciprocal.strict_bound y hy)

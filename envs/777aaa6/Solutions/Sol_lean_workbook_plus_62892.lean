-- Prove2me | solution 1 for lean_workbook_plus_62892
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:02:22.148055+00:00
-- url     : https://prove2.me/submissions/d87f65c2-b880-4199-b8f0-30b762b722f1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace SharpQuarticMaximum

theorem gap_identity (a : ℝ) :
    27 / 256 - (a ^ 3 - a ^ 4) =
      (a - 3 / 4) ^ 2 * ((a + 1 / 4) ^ 2 + 1 / 8) := by ring

theorem bound (a : ℝ) : a ^ 3 - a ^ 4 ≤ 27 / 256 := by
  have h := mul_nonneg (sq_nonneg (a - 3 / 4))
    (show 0 ≤ (a + 1 / 4) ^ 2 + 1 / 8 by positivity)
  linarith [gap_identity a]

theorem equality_iff (a : ℝ) : a ^ 3 - a ^ 4 = 27 / 256 ↔ a = 3 / 4 := by
  constructor
  · intro h
    have hpos : 0 < (a + 1 / 4) ^ 2 + 1 / 8 := by positivity
    have hz : (a - 3 / 4) ^ 2 * ((a + 1 / 4) ^ 2 + 1 / 8) = 0 := by
      linarith [gap_identity a]
    have hs := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hpos)
    nlinarith [sq_nonneg (a - 3 / 4)]
  · rintro rfl
    norm_num

end SharpQuarticMaximum

theorem solution (a : ℝ) (ha : 0 < a) : a ^ 3 - a ^ 4 ≤ 27 / 256 :=
  SharpQuarticMaximum.bound a

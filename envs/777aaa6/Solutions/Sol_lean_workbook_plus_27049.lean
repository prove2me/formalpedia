-- Prove2me | solution 1 for lean_workbook_plus_27049
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:00:33.605668+00:00
-- url     : https://prove2.me/submissions/430491d2-407d-4f65-ba38-ddafcf259eea

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    |x * (x - 1) * (x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2 + 4)| < 5 / 2 := by
  by_cases he : x = 1
  · subst x
    norm_num
  have hx1 : x < 1 := lt_of_le_of_ne hx.2 he
  have h2 : x ^ 2 < 1 := pow_lt_one₀ hx.1 hx1 (by decide)
  have h4 : x ^ 4 < 1 := pow_lt_one₀ hx.1 hx1 (by decide)
  have h6 : x ^ 6 < 1 := pow_lt_one₀ hx.1 hx1 (by decide)
  have hp : 0 ≤ x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2 + 4 := by positivity
  have hpu : x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2 + 4 < 10 := by linarith
  have hq : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hn : x * (x - 1) * (x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2 + 4) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hx.1 (by linarith [hx.2])) hp
  rw [abs_of_nonpos hn]
  calc
    -(x * (x - 1) * (x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2 + 4)) =
        x * (1 - x) * (x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2 + 4) := by ring
    _ ≤ 1 / 4 * (x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2 + 4) :=
      mul_le_mul_of_nonneg_right hq hp
    _ < 5 / 2 := by linarith

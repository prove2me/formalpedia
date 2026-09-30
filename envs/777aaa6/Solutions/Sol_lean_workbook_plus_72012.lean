-- Prove2me | solution 1 for lean_workbook_plus_72012
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:34:53.490556+00:00
-- url     : https://prove2.me/submissions/76d5056a-2f50-474c-ba22-31cd610bb9cd

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

theorem solution {a b : ℝ} (h1 : a > b) (h2 : b > 0)
    (h3 : a ^ 5 + b ^ 5 = a - b) : a ^ 4 + 2 * b ^ 4 < 1 := by
  have ha : 0 < a := lt_trans h2 h1
  have ha1 : a < 1 := by
    by_contra hn
    have hp := le_self_pow₀ (le_of_not_gt hn) (by decide : (5 : ℕ) ≠ 0)
    linarith [pow_pos h2 5]
  have hb1 : b < 1 := lt_trans h1 ha1
  have hab : a * b < 1 := calc
    a * b < a * 1 := mul_lt_mul_of_pos_left hb1 ha
    _ = a := mul_one a
    _ < 1 := ha1
  have hgap : 0 < 1 - a * b := by linarith
  have hs : 0 < 2 * b ^ 2 * (1 - a * b) :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_pos h2)) hgap
  have hn : 0 < b * ((b ^ 2 - 1) ^ 2 + 2 * b ^ 2 * (1 - a * b)) :=
    mul_pos h2 (add_pos_of_nonneg_of_pos (sq_nonneg _) hs)
  have hid : a * (1 - a ^ 4 - 2 * b ^ 4) =
      b * ((b ^ 2 - 1) ^ 2 + 2 * b ^ 2 * (1 - a * b)) := by
    linear_combination -h3
  have hp : 0 < a * (1 - a ^ 4 - 2 * b ^ 4) := by rw [hid]; exact hn
  have := (mul_pos_iff_of_pos_left ha).mp hp
  linarith

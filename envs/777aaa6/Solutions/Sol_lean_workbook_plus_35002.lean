-- Prove2me | solution 1 for lean_workbook_plus_35002
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:42:25.959696+00:00
-- url     : https://prove2.me/submissions/e9b46227-f367-471a-a981-535f488a28d6

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (f : ℝ → ℝ)
    (hf : ∀ x, x ≠ 0 ∧ x ≠ 1 →
      f x + f ((1 : ℝ) / (1 - x)) = (2 * x - 1)^2 + f (1 - (1 : ℝ) / x)) :
    f 3 = 113 / 9 := by
  have h1 : f 3 + f (-1 / 2) = 25 + f (2 / 3) := by
    convert hf 3 (by norm_num) using 1 <;> norm_num <;> rfl
  have h2 : f (2 / 3) + f 3 = 1 / 9 + f (-1 / 2) := by
    convert hf (2 / 3) (by norm_num) using 1 <;> norm_num <;> rfl
  linarith only [h1, h2]

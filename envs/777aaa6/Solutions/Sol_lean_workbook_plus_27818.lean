-- Prove2me | solution 1 for lean_workbook_plus_27818
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:53:26.842294+00:00
-- url     : https://prove2.me/submissions/6ed07944-d043-4c7c-a7e2-81d5937b99d9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem nonnegative_product (a b : Real) (hab : 0 ≤ a * b) :
    3 * a ^ 6 + 16 * a ^ 3 * b ^ 3 + 3 * b ^ 6 ≥
      11 * a ^ 4 * b ^ 2 + 11 * a ^ 2 * b ^ 4 := by
  have hid : 3 * a ^ 6 + 16 * a ^ 3 * b ^ 3 + 3 * b ^ 6 -
      (11 * a ^ 4 * b ^ 2 + 11 * a ^ 2 * b ^ 4) =
      (a - b) ^ 2 * (3 * (a ^ 2 - b ^ 2) ^ 2 +
        6 * (a * b) * (a ^ 2 + b ^ 2) + 4 * (a * b) ^ 2) := by
    ring
  have hn : 0 ≤ (a - b) ^ 2 * (3 * (a ^ 2 - b ^ 2) ^ 2 +
      6 * (a * b) * (a ^ 2 + b ^ 2) + 4 * (a * b) ^ 2) := by positivity
  linarith only [hid, hn]

theorem solution : ¬ (∀ a b : Real,
    3 * a ^ 6 + 16 * a ^ 3 * b ^ 3 + 3 * b ^ 6 ≥
      11 * a ^ 4 * b ^ 2 + 11 * a ^ 2 * b ^ 4) := by
  intro h
  have hc := h 1 (-1)
  have hl : (3 : Real) * 1 ^ 6 + 16 * 1 ^ 3 * (-1) ^ 3 + 3 * (-1) ^ 6 = -10 := by
    ring
  have hr : (11 : Real) * 1 ^ 4 * (-1) ^ 2 + 11 * 1 ^ 2 * (-1) ^ 4 = 22 := by
    ring
  rw [hl, hr] at hc
  norm_num at hc

#print axioms solution

-- Prove2me | solution 1 for lean_workbook_plus_69520
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:53:00.465712+00:00
-- url     : https://prove2.me/submissions/54420231-2edb-4356-9572-47425230b113

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a * b < 0) :
  |a + b| ≤ max (|a|) (|b|) := by
  rcases mul_neg_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [abs_of_pos ha, abs_of_neg hb]
    apply abs_le.mpr
    constructor <;> linarith [le_max_left a (-b), le_max_right a (-b)]
  · rw [abs_of_neg ha, abs_of_pos hb]
    apply abs_le.mpr
    constructor <;> linarith [le_max_left (-a) b, le_max_right (-a) b]

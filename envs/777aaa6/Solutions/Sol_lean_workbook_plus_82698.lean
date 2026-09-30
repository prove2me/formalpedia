-- Prove2me | solution 1 for lean_workbook_plus_82698
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:29:28.088623+00:00
-- url     : https://prove2.me/submissions/28391369-46c6-4fa9-925e-0569c3540bd4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (a b c d : ℝ) (hab : a * b = 1) (h : a * c + b * d = 2) :
    1 - c * d ≥ 0 := by
  have hprod : (a * c) * (b * d) = c * d := by
    calc
      (a * c) * (b * d) = (a * b) * (c * d) := by ring
      _ = c * d := by rw [hab, one_mul]
  have hsq : (a * c + b * d) ^ 2 = 4 := by rw [h]; norm_num
  nlinarith [sq_nonneg (a * c - b * d)]

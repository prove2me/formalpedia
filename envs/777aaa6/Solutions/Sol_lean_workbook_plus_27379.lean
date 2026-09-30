-- Prove2me | solution 1 for lean_workbook_plus_27379
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:58:57.963928+00:00
-- url     : https://prove2.me/submissions/6ab030ed-aa23-4374-829b-5af9680c70d4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b : ℝ) (ha : 1 ≤ a ∧ a ≤ 2)
    (hb : 1 ≤ b ∧ b ≤ 2) : 2 * (a + b) ^ 2 ≤ 9 * a * b := by
  have hab : 0 ≤ 2 * a - b := by linarith [ha.1, hb.2]
  have hba : 0 ≤ 2 * b - a := by linarith [hb.1, ha.2]
  nlinarith [mul_nonneg hab hba]

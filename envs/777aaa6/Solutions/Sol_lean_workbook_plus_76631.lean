-- Prove2me | solution 1 for lean_workbook_plus_76631
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:48.906176+00:00
-- url     : https://prove2.me/submissions/f4d400af-362e-4613-bfd6-4c49cf4ee3b5

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    9 / (a + b + c) ≤ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by
  have hs : 0 < a + b + c := by positivity
  have hab : 0 < a + b := by positivity
  have hbc : 0 < b + c := by positivity
  have hca : 0 < c + a := by positivity
  have identity :
      2 * (a + b + c) * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) - 9 =
        ((a - c) ^ 2 * (c + a) + (b - a) ^ 2 * (a + b) +
          (c - b) ^ 2 * (b + c)) / ((a + b) * (b + c) * (c + a)) := by
    field_simp [ne_of_gt hab, ne_of_gt hbc, ne_of_gt hca]
    <;> ring
  have hnonneg : 0 ≤
      ((a - c) ^ 2 * (c + a) + (b - a) ^ 2 * (a + b) +
        (c - b) ^ 2 * (b + c)) / ((a + b) * (b + c) * (c + a)) := by positivity
  apply (div_le_iff₀ hs).mpr
  nlinarith [identity]

#print axioms solution

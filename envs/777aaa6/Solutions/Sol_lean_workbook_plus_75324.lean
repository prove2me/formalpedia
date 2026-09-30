-- Prove2me | solution 1 for lean_workbook_plus_75324
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:29:56.874518+00:00
-- url     : https://prove2.me/submissions/565b0c8f-aef6-418f-b38b-a232989a1ef3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution :
    ((Real.sqrt 2 / 2) ^ 3 * (-Real.sqrt 2 / 2) ^ 3) /
      ((1 + (Real.sqrt 2 / 2) ^ 6) * (1 + (-Real.sqrt 2 / 2) ^ 6)) = -8 / 81 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h2 : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by nlinarith
  have h6 : (Real.sqrt 2 / 2) ^ 6 = (1 : ℝ) / 8 := by
    calc
      _ = ((Real.sqrt 2 / 2) ^ 2) ^ 3 := by ring
      _ = (1 : ℝ) / 8 := by rw [h2]; norm_num
  have hn : (-Real.sqrt 2 / 2) ^ 6 = (Real.sqrt 2 / 2) ^ 6 := by ring
  have hp : (Real.sqrt 2 / 2) ^ 3 * (-Real.sqrt 2 / 2) ^ 3 =
      -(Real.sqrt 2 / 2) ^ 6 := by ring
  rw [hp, hn, h6]
  norm_num

#print axioms solution

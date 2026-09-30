-- Prove2me | solution 1 for lean_workbook_plus_62132
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:08:05.857662+00:00
-- url     : https://prove2.me/submissions/9608857c-a41d-443b-863a-686fa2ba74ea

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

theorem solution (A : Matrix (Fin 2) (Fin 2) ℚ)
    (hA : A = !![9 / 2, 7 / 2; -7 / 2, -5 / 2]) :
    A * !![-5 / 2, -7 / 2; 7 / 2, 9 / 2] = 1 := by
  rw [hA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

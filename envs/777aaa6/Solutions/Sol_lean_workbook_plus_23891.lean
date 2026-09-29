-- Prove2me | solution 1 for lean_workbook_plus_23891
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:37.625183+00:00
-- url     : https://prove2.me/submissions/79f548c1-93ee-4f4e-8c64-342af2284976

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (T U : Matrix (Fin 2) (Fin 2) ℚ) (hT : T =![![1, 0],![0, 0]]) (hU : U =![![0, 1],![0, 1]]) : T * U =![![0, 1],![0, 0]] := by
  rw [hT,hU]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_two]

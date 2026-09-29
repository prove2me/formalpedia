-- Prove2me | solution 1 for lean_workbook_plus_60484
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:58.65495+00:00
-- url     : https://prove2.me/submissions/dd744b29-edc0-490a-b27f-6b695a66e0a2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (A B : Matrix (Fin 2) (Fin 2) ℚ) (hA : A =![![1, 0],![0, 0]]) (hB : B =![![0, 0],![0, 1]]) : A * B =![![0, 0],![0, 0]] := by
  subst A
  subst B
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

-- Prove2me | solution 1 for lean_workbook_plus_4482
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:07:38.867269+00:00
-- url     : https://prove2.me/submissions/b39c20e9-4f39-4033-8e2d-eb2953c9dc82

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (A B : Matrix (Fin 2) (Fin 2) ℚ) (hA : A =![![1, 1],![0, 0]]) (hB : B =![![1, 1],![0, 0]]) : A * B = B * A ∧ A * B = A^2 ∧ A * B = A := by
  rw [hA,hB]
  refine ⟨?_,?_,?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [pow_two,Matrix.mul_apply,Fin.sum_univ_two]

-- Prove2me | solution 1 for lean_workbook_plus_47445
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:07:36.912699+00:00
-- url     : https://prove2.me/submissions/fea7a5fd-6e6d-43a7-9bbe-aa19e936fc53

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (A B : Matrix (Fin 2) (Fin 2) ℚ) (hA : A =![![1, 1],![0, 0]]) (hB : B =![![0, 0],![1, 1]]) : A ^ 2 = A * B ∧ B ^ 2 = B * A := by
  have fullSource : A^2=A ∧ A*B=A ∧ B^2=B ∧ B*A=B := by
    rw [hA,hB]
    refine ⟨?_,?_,?_,?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [pow_two,Matrix.mul_apply,Fin.sum_univ_two]
  exact ⟨fullSource.1.trans fullSource.2.1.symm,fullSource.2.2.1.trans fullSource.2.2.2.symm⟩

-- Prove2me | solution 1 for lean_workbook_plus_70457
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:08:05.081646+00:00
-- url     : https://prove2.me/submissions/da396f61-1397-4b66-9947-bff1b261d595

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem solution (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A = !![Real.sqrt 3 / 2, -1 / 2; 1 / 2, Real.sqrt 3 / 2]) :
    ∃ n : ℕ, A ^ n = 1 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt 3)^3 = 3 * Real.sqrt 3 := by
    calc
      (Real.sqrt 3)^3 = Real.sqrt 3 * (Real.sqrt 3)^2 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hs]; ring
  have hcube : A^3 = !![0, -1; 1, 0] := by
    rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      nlinarith! only [hs, hc]
  refine ⟨12, ?_⟩
  rw [show (12 : ℕ) = 3 * 4 from rfl, pow_mul, hcube]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] <;> rfl

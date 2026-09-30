-- Prove2me | solution 1 for lean_workbook_plus_38120
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:57:11.666009+00:00
-- url     : https://prove2.me/submissions/60c2c170-676b-4560-b873-81664667ec51

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false

theorem solution (R : Type*) [Field R] (A B : Matrix (Fin 2) (Fin 2) R) :
    !![1, 0; B, 1] * !![A * B - 1, A; 0, -1] * !![1, 0; -B, 1] =
      !![-1, A; 0, B * A - 1] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

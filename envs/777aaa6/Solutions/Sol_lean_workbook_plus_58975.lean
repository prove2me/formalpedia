-- Prove2me | solution 1 for lean_workbook_plus_58975
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:40.23924+00:00
-- url     : https://prove2.me/submissions/63dddc66-286f-452a-b674-1988cf684a6b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (X : Matrix (Fin 2) (Fin 2) ℝ) : ∃ a b c d : ℝ, X =!![a, b; c, d] := by
  refine ⟨X 0 0,X 0 1,X 1 0,X 1 1,?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

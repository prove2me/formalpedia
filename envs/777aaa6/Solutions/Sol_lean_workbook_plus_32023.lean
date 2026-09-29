-- Prove2me | solution 1 for lean_workbook_plus_32023
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:56.995276+00:00
-- url     : https://prove2.me/submissions/f90325bd-f585-4344-b489-17978991871a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ c : ℝ, (-3*c^2 + 5*c - 3*c)^2 - 4*(c^2 - 3*c + 3)*(3*c^2 - 3*c + 1) ≤ 0) := by
  push_neg
  refine ⟨(2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

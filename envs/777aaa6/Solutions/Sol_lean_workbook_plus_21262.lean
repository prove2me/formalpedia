-- Prove2me | solution 1 for lean_workbook_plus_21262
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:51:07.651929+00:00
-- url     : https://prove2.me/submissions/d46d237b-de39-4cae-99c4-2a18f61644eb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c x y z : ℝ, a * b * c * (x * y + y * z + z * x) ≥ x * y * z * (a * b + b * c + c * a)) := by
  push_neg
  refine ⟨(-2), ?_⟩
  refine ⟨(3/2), ?_⟩
  refine ⟨(-4), ?_⟩
  refine ⟨(5/2), ?_⟩
  refine ⟨(-1/2), ?_⟩
  refine ⟨(-10), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

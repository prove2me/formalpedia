-- Prove2me | solution 1 for lean_workbook_plus_30300
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:38.318355+00:00
-- url     : https://prove2.me/submissions/8dc32f8e-e25a-4ffc-8c17-5d1ec729eda7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (a^2/(a^2 + a * b + b^2) + b^2/(b^2 + b * c + c^2) + c^2/(c^2 + c * a + a^2) : ℝ) ≥ (a + b + c) / 3) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_14134
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:40:39.538194+00:00
-- url     : https://prove2.me/submissions/71d062a7-caa4-4b24-b071-8bfd26a15bfb

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
theorem solution : ¬ (∀ x : ℝ, x * Real.sqrt ((x - 1) / (x + 1)) = (x / (x + 1)) * Real.sqrt (x ^ 2 - 1)) := by
  push_neg
  refine ⟨(-2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith | grind

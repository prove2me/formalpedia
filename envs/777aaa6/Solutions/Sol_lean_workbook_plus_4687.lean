-- Prove2me | solution 1 for lean_workbook_plus_4687
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:53.059555+00:00
-- url     : https://prove2.me/submissions/32b62b85-8dcd-471d-b880-7d6079033234

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
theorem solution : ¬ (∀ a b c : ℝ, (a / (a ^ 2 + 2 * b * c) + b / (b ^ 2 + 2 * c * a) + c / (c ^ 2 + 2 * a * b) ≤ (a + b + c) / (a * b + b * c + a * c))) := by
  push_neg
  refine ⟨(1), ?_⟩
  refine ⟨(0), ?_⟩
  refine ⟨(0), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith | grind

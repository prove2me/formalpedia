-- Prove2me | solution 1 for lean_workbook_plus_72856
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:58.943082+00:00
-- url     : https://prove2.me/submissions/618f8b18-cbcf-445a-9c8d-b2c4fcb2ec7c

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
theorem solution : ¬ (∀ a b c : ℝ, (a * b + b * c + c * a) * (a + b + c) + (a * b + b * c + c * a) + 6 ≥ 6 * (a + b + c)) := by
  push_neg
  refine ⟨(-2), ?_⟩
  refine ⟨(-2), ?_⟩
  refine ⟨(-2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith | grind

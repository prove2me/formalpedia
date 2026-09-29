-- Prove2me | solution 1 for lean_workbook_plus_3729
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:54.079517+00:00
-- url     : https://prove2.me/submissions/4f191ba9-a1f1-4bd4-8687-d3ce216ea727

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
theorem solution : ¬ (∀ a b c : ℝ, (a / (a + b) + b / (b + c) + c / (c + a)) < 2) := by
  push_neg
  refine ⟨(5), ?_⟩
  refine ⟨(-4), ?_⟩
  refine ⟨(3/4), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

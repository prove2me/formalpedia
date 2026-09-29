-- Prove2me | solution 1 for lean_workbook_plus_24200
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:56:13.06841+00:00
-- url     : https://prove2.me/submissions/6e6e79bf-08d3-4501-86f2-7b274faad373

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
theorem solution : ¬ (∀ a b c : ℝ, (a / (a + b)) ^ 3 + (b / (b + c)) ^ 3 + (c / (c + a)) ^ 3 ≤ 9 / 8) := by
  push_neg
  refine ⟨(-1/2), ?_⟩
  refine ⟨(9), ?_⟩
  refine ⟨(3/4), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

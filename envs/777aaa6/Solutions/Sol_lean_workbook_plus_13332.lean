-- Prove2me | solution 1 for lean_workbook_plus_13332
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:58:35.217744+00:00
-- url     : https://prove2.me/submissions/abf34f86-f77f-401f-bc39-26cbd1e59068

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
theorem solution : ¬ (∀ b c : ℝ, (b + c) ^ 4 - b ^ 4 - c ^ 4 - 14 * b ^ 2 * c ^ 2 ≥ 0) := by
  push_neg
  refine ⟨(5), ?_⟩
  refine ⟨(-2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

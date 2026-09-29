-- Prove2me | solution 1 for lean_workbook_plus_22268
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:58:19.688506+00:00
-- url     : https://prove2.me/submissions/40f58bdb-6f98-4478-be3c-39c52bb5b4b2

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
theorem solution : ¬ (∀ a b c : ℝ, (a * b + b * c + c * a) * (a ^ 2 + b ^ 2 + c ^ 2 + a + b + c) ≤ 6 * (a ^ 2 + b ^ 2 + c ^ 2)) := by
  push_neg
  refine ⟨(2), ?_⟩
  refine ⟨(2), ?_⟩
  refine ⟨(2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

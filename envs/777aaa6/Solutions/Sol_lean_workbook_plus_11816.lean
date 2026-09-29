-- Prove2me | solution 1 for lean_workbook_plus_11816
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:49.710372+00:00
-- url     : https://prove2.me/submissions/c9b7ae19-ce0f-4836-abd6-51ddbea874e6

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
theorem solution : ¬ (∀ a : ℤ, 289 ∣ (a^2 - 3*a - 19 - 17*(a - 7))) := by
  push_neg
  refine ⟨(0), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

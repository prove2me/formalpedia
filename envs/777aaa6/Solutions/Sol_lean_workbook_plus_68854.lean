-- Prove2me | solution 1 for lean_workbook_plus_68854
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:12.172471+00:00
-- url     : https://prove2.me/submissions/db0beb05-744f-49d0-9afb-5c88198e2de2

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
theorem solution : ¬ (∀ u : ℝ, 12 * u ^ 5 + 60 * u ^ 4 + 87 * u ^ 3 + 21 * u ^ 2 - 72 * u - 54 + 16 * Real.sqrt 3 * u ^ 2 + 32 * Real.sqrt 3 * u + 32 * Real.sqrt 3 ≥ (21 + 16 * Real.sqrt 3) * u ^ 2 - (72 - 32 * Real.sqrt 3) * u + 32 * Real.sqrt 3 - 54) := by
  push_neg
  refine ⟨(-1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith | grind

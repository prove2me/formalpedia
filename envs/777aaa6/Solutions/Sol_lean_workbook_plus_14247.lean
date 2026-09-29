-- Prove2me | solution 1 for lean_workbook_plus_14247
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:00:14.216557+00:00
-- url     : https://prove2.me/submissions/0fcd3aaf-2e3f-46db-bd9e-4fcbafa3df53

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
theorem solution : ¬ (∀ x c : ℝ, 6 - 5 * x + 6 * c + 3 * x^2 - 3 * c^2 ≥ 0) := by
  push_neg
  refine ⟨(-10), ?_⟩
  refine ⟨(-10), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

-- Prove2me | solution 1 for lean_workbook_plus_62176
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:50.789639+00:00
-- url     : https://prove2.me/submissions/538a51e6-4d2e-4537-b44c-fd39ac1dd24e

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
theorem solution : ¬ (∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 + x + y + z >= x ^ 2 + y ^ 2 + z ^ 2 + 3 ∧ x ^ 2 + y ^ 2 + z ^ 2 + 3 >= 2 * (x * y + x * z + y * z)) := by
  push_neg
  refine ⟨(0), ?_⟩
  refine ⟨(0), ?_⟩
  refine ⟨(0), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

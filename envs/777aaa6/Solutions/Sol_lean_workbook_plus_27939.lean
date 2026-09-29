-- Prove2me | solution 1 for lean_workbook_plus_27939
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:55:56.710117+00:00
-- url     : https://prove2.me/submissions/f62058aa-7d37-42ff-bb49-27d7ac56d316

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
theorem solution : ¬ (∀ a b c : ℝ, 12 * a ^ 6 + 31 * a ^ 5 * b + 4 * a ^ 5 * c - 38 * a ^ 4 * b ^ 2 + 9 * a ^ 4 * b * c + 16 * a ^ 4 * c ^ 2 - 33 * a ^ 3 * b ^ 3 - 20 * a ^ 3 * b ^ 2 * c + 61 * a ^ 3 * b * c ^ 2 - 33 * a ^ 3 * c ^ 3 + 16 * a ^ 2 * b ^ 4 + 61 * a ^ 2 * b ^ 3 * c - 126 * a ^ 2 * b ^ 2 * c ^ 2 - 20 * a ^ 2 * b * c ^ 3 - 38 * a ^ 2 * c ^ 4 + 4 * a * b ^ 5 + 9 * a * b ^ 4 * c - 20 * a * b ^ 3 * c ^ 2 + 61 * a * b ^ 2 * c ^ 3 + 9 * a * b * c ^ 4 + 31 * a * c ^ 5 + 12 * b ^ 6 + 31 * b ^ 5 * c - 38 * b ^ 4 * c ^ 2 - 33 * b ^ 3 * c ^ 3 + 16 * b ^ 2 * c ^ 4 + 4 * b * c ^ 5 + 12 * c ^ 6 ≥ 0) := by
  push_neg
  refine ⟨(-2), ?_⟩
  refine ⟨(4/3), ?_⟩
  refine ⟨(2/3), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

-- Prove2me | solution 1 for lean_workbook_plus_73943
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:59.603684+00:00
-- url     : https://prove2.me/submissions/0af71fdc-95a0-41e1-a01a-9ae2f8b50232

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
theorem solution : ¬ (∀ a b c : ℝ, a ^ 4 + b ^ 4 + c ^ 4 + 4 * a ^ 2 * c ^ 2 + 4 * b ^ 2 * c ^ 2 + 4 * c ^ 2 * a ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 ≥ 2 * a ^ 3 * (b + c) + 2 * b ^ 3 * (a + c) + 2 * c ^ 3 * (a + b) + 6 * a * b * c) := by
  push_neg
  refine ⟨(6), ?_⟩
  refine ⟨(5), ?_⟩
  refine ⟨(0), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

-- Prove2me | solution 1 for lean_workbook_plus_65601
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:58.970774+00:00
-- url     : https://prove2.me/submissions/37517a9b-7fb1-49bc-a57d-a867b0ce89cf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 + b^2 + c^2) / (a + b + c)^2 + 2 * a * b / (a + b)^2 + 2 * b * c / (b + c)^2 + 2 * c * a / (c + a)^2 ≤ 11 / 6) := by
  push_neg
  refine ⟨(-3), ?_⟩
  refine ⟨(2), ?_⟩
  refine ⟨(2/3), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

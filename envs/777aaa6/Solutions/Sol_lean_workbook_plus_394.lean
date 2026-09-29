-- Prove2me | solution 1 for lean_workbook_plus_394
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:25.328498+00:00
-- url     : https://prove2.me/submissions/62c48c7c-6ec1-42c9-a839-68c0ef16009e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, 4 * (a * b^2 * c^3 + b * c^2 * a^3 + c * a^2 * b^3) + 2 * (b * c^5 + c * a^5 + a * b^5) + 2 * (a^2 * c^4 + b^2 * a^4 + c^2 * b^4) ≥ 6 * a^2 * b^2 * c^2 + 3 * (a * b * c^4 + b * c * a^4 + c * a * b^4) + 3 * (a^3 * b^3 + b^3 * c^3 + c^3 * a^3)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  2 , ?_⟩
  norm_num at *

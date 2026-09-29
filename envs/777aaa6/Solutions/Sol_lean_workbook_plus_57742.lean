-- Prove2me | solution 1 for lean_workbook_plus_57742
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:29:31.111045+00:00
-- url     : https://prove2.me/submissions/4c7cc756-9523-4602-a86b-34acff32860f

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 → (x^2*y + y^2*z + z^2*x) * (1/(x-y)^2 + 1/(y-z)^2 + 1/(z-x)^2) ≥ 4/5 * (x + y + z)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

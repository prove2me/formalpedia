-- Prove2me | solution 1 for lean_workbook_plus_58461
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:46.004183+00:00
-- url     : https://prove2.me/submissions/1469ad7e-5465-419b-9aad-dd7391b3d2b8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^3 + b^3 + c^3) * (a * b + b * c + c * a)^2 ≥ 3 * a * b * c * (a^2 + b^2 + c^2)^2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  2 , ?_⟩
  norm_num at *

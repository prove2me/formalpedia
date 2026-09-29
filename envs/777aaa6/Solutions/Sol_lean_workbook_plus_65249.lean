-- Prove2me | solution 1 for lean_workbook_plus_65249
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:18.208169+00:00
-- url     : https://prove2.me/submissions/acf6fb91-b03e-4321-b2d2-4490503dfe19

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 / b + b^2 / c + c^2 / a)^2 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ (a^2 + b^2 + c^2)^3) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

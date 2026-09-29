-- Prove2me | solution 1 for lean_workbook_plus_1269
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:21.069938+00:00
-- url     : https://prove2.me/submissions/06230e28-e0e5-4938-afd2-8eb628991c89

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (Real.sqrt a * Real.sqrt b * Real.sqrt c) * (a + b + c - 2) ≥ (2 * (1 - 3 * a * b * c - (Real.sqrt (b * c))^3 - (Real.sqrt (c * a))^3 - (Real.sqrt (a * b))^3)) / (Real.sqrt a + Real.sqrt b + Real.sqrt c)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

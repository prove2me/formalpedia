-- Prove2me | solution 1 for lean_workbook_plus_13190
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:30.381524+00:00
-- url     : https://prove2.me/submissions/6986d052-c439-4cc0-a2a4-99a75d659677

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a + b + c) ^ 2 / (a + b + c + a * b + b * c + c * a) ≥ 3 * (a + b + c) ^ 2 / (3 * (a + b + c) + (a + b + c) ^ 2)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
  refine ⟨ -  2 , ?_⟩
  norm_num at *

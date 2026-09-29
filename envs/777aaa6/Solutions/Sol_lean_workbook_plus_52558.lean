-- Prove2me | solution 1 for lean_workbook_plus_52558
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:09.643018+00:00
-- url     : https://prove2.me/submissions/0ab6bae8-6ea5-4710-b241-835dc2865a21

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, 2 * a / (21 * a + 75 * b) + 2 * b / (21 * b + 75 * c) + 2 * c / (21 * c + 75 * a) + 1 / 7 + 1 / 10 * Real.sqrt ((a * b + a * c + b * c) / (a ^ 2 + b ^ 2 + c ^ 2)) ≤ 5 * Real.sqrt (a ^ 2 + 3 * a * b) / (21 * a + 75 * b) + 5 * Real.sqrt (b ^ 2 + 3 * b * c) / (21 * b + 75 * c) + 5 * Real.sqrt (3 * a * c + c ^ 2) / (21 * c + 75 * a)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

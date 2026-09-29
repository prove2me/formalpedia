-- Prove2me | solution 1 for lean_workbook_plus_17055
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:49:27.002282+00:00
-- url     : https://prove2.me/submissions/e97a2923-72e0-44b5-b0a7-dff4b92ea507

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, 8 * a ^ 3 * b ^ 3 * c ^ 3 < (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2 - 8 * a ^ 2 * b ^ 2 * c ^ 2)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_14445
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:19.416612+00:00
-- url     : https://prove2.me/submissions/d6814e11-15f0-4245-a4ec-641de249b767

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c d : ℝ, a * b ^ 4 * c + b * c ^ 4 * d + a * c * d ^ 4 + a ^ 4 * b * d ≥ a * b * c * d * (a ^ 2 + c ^ 2 + b ^ 2 + d ^ 2)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

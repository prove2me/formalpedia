-- Prove2me | solution 1 for lean_workbook_plus_37958
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:34:25.29687+00:00
-- url     : https://prove2.me/submissions/d5b25f16-8dec-4da5-a397-153cc2728391

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, 2 * (a ^ 5 + b ^ 5 + c ^ 5) ≥ a * b ^ 4 + b * c ^ 4 + c * a ^ 4 + a ^ 4 * b + b ^ 4 * c + c ^ 4 * a) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

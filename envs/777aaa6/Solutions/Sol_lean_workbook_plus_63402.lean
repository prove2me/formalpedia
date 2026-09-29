-- Prove2me | solution 1 for lean_workbook_plus_63402
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:23:21.754102+00:00
-- url     : https://prove2.me/submissions/5d330ab3-3367-409a-bf51-e95105eeb630

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, 9 + (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 6 * 3) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_22083
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:58:56.634915+00:00
-- url     : https://prove2.me/submissions/d4601353-2d66-4658-b2ea-e02d21646b70

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 / b + b^2 / c + c^2 / a) ≥ a + b + c) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

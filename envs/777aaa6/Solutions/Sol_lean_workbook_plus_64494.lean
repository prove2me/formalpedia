-- Prove2me | solution 1 for lean_workbook_plus_64494
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:32:25.289748+00:00
-- url     : https://prove2.me/submissions/458e3ae5-d288-44c8-a875-03bcc5108f15

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a + b + c) * (1 / a + 2 / b + 1 / c) ≤ 15) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  4  ) , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_634
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:48.136267+00:00
-- url     : https://prove2.me/submissions/88c28734-1ca5-4e17-95ba-133ff9839f5e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a + b + c) / (1 + b * c) ≤ 2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *

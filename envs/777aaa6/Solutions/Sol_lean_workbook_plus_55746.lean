-- Prove2me | solution 1 for lean_workbook_plus_55746
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:51.246719+00:00
-- url     : https://prove2.me/submissions/e64ecbaa-e8a9-4d59-9661-3060fbac32cf

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a * b + b * c + c * a - a * b * c ≤ 28 / 27) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *

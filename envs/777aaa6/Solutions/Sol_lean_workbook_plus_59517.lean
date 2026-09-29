-- Prove2me | solution 1 for lean_workbook_plus_59517
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:07:30.201686+00:00
-- url     : https://prove2.me/submissions/0513c424-3db5-4fcd-8aab-f5e8c5873382

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a^2 * b^2 + a^2 * c^2 - a^4 + b^4 + b^2 * c^2 - a^2 * b^2 + b^2 * c^2 + c^4 - a^2 * c^2 - 3 * b^2 * c^2 = 0) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

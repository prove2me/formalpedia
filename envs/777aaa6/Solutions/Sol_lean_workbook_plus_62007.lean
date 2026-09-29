-- Prove2me | solution 1 for lean_workbook_plus_62007
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:14:57.513512+00:00
-- url     : https://prove2.me/submissions/379c4991-a394-491a-bae3-203d45ecfd3a

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ n : ℕ, ∀ a : ℝ, (1 + a / (n + 1)) ^ (n + 1) > (1 + a / n) ^ n) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

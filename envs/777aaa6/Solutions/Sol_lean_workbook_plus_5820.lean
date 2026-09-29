-- Prove2me | solution 1 for lean_workbook_plus_5820
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:38:27.718257+00:00
-- url     : https://prove2.me/submissions/6c9ece74-41c2-4b3f-9832-a4d685f7b6e0

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a^2 + b^2 + c^2 > a^2 + (a - 1)^2 + 1) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

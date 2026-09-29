-- Prove2me | solution 1 for lean_workbook_plus_61201
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:44:00.631028+00:00
-- url     : https://prove2.me/submissions/eec2d63e-a4aa-4893-8b6c-59f65678083f

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 + b^2) / (a + b) + (b^2 + c^2) / (b + c) + (c^2 + a^2) / (c + a) ≥ 3) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_44050
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:36:27.423759+00:00
-- url     : https://prove2.me/submissions/950e72b2-8a51-46f0-b29c-a597f3e7a637

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ c d : ℝ, (c^3 + 3) * (d^3 + 3) ≥ 8 + (c + d)^3) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

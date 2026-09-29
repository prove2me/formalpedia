-- Prove2me | solution 1 for lean_workbook_plus_34650
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:48.852463+00:00
-- url     : https://prove2.me/submissions/059783c6-9ae4-4f68-bddf-0855fe830aa0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a + 1 / (a + 4)) * (b + 9 / b) * (c + 1 / (c + 4)) > 3) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

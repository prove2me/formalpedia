-- Prove2me | solution 1 for lean_workbook_plus_65626
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:01:20.504981+00:00
-- url     : https://prove2.me/submissions/00bf53a6-e93c-4942-ac20-0e36b7f0aadc

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (1 / (a + b * c) + 1 / (b + c * a) + 1 / (c + a * b) ≥ 3 / 2)) := by
  push_neg
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num

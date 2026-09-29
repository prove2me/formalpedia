-- Prove2me | solution 1 for lean_workbook_plus_19855
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:21.532988+00:00
-- url     : https://prove2.me/submissions/7c28adcb-1981-41af-b4a6-961a74968352

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a * b + b * c + c * a) * (a ^ 4 + b ^ 4 + c ^ 4) ≥ 3 * (a ^ 2 * b ^ 4 + b ^ 2 * c ^ 4 + c ^ 2 * a ^ 4)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

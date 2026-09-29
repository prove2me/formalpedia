-- Prove2me | solution 1 for lean_workbook_plus_10279
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:31:01.998151+00:00
-- url     : https://prove2.me/submissions/44b8154b-454e-4965-b984-7c11ce582354

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (2 * (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) - 6 + (9 * (a + b + c) ^ 2) / (a ^ 2 + b ^ 2 + c ^ 2) - 27) ≥ 0) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

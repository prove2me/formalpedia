-- Prove2me | solution 1 for lean_workbook_plus_63196
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:15:49.906832+00:00
-- url     : https://prove2.me/submissions/b6fe066c-8fd3-435a-ae79-31379d932f6b

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, x^2 + y^2 + z^2 ≥ (x + y + z) / 2 ∧ (x + y + z) / 2 ≥ (3 - x - y - z) / 2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  3  ) , ?_⟩
  norm_num at *

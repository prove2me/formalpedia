-- Prove2me | solution 1 for lean_workbook_plus_75507
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:05:23.324163+00:00
-- url     : https://prove2.me/submissions/83be7df9-069e-4e54-9e57-6d7f4b734594

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (1 / (a ^ 2 + a + 1) + 1 / (b ^ 2 + b + 1) + 1 / (c ^ 2 + c + 1)) ≥ 1) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *

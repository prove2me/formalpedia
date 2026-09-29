-- Prove2me | solution 1 for lean_workbook_plus_23198
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:12:50.906097+00:00
-- url     : https://prove2.me/submissions/272def90-a464-446a-b37e-bef06eba8c36

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 + b^2 * c) / (b + c) + (b^2 + c^2 * a) / (a + c) + (c^2 + a^2 * b) / (a + b) ≥ 2 / 3) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

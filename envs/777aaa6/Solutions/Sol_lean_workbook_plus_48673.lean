-- Prove2me | solution 1 for lean_workbook_plus_48673
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:12:50.866501+00:00
-- url     : https://prove2.me/submissions/84b51559-b464-47e2-9742-a372244897f8

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
theorem solution : ¬ (∀ a b c : ℝ, (a^2 / (b + 1) / (c + 1) + b^2 / (c + 1) / (a + 1) + c^2 / (a + 1) / (b + 1) + 2 * a * b * c / (a + 1) / (b + 1) / (c + 1)) ≥ 1) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

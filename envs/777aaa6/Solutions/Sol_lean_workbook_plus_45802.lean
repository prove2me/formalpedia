-- Prove2me | solution 1 for lean_workbook_plus_45802
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:13:49.285743+00:00
-- url     : https://prove2.me/submissions/d9a00d9c-44c3-4ca7-a99e-663898281bd6

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
theorem solution : ¬ (∀ x y z : ℝ, (1 + y) * (1 + z) / (1 + x) + (1 + z) * (1 + x) / (1 + y) + (1 + x) * (1 + y) / (1 + z) ≥ 3 + x + y + z) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  2 , ?_⟩
  norm_num at *

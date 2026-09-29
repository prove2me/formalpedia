-- Prove2me | solution 1 for lean_workbook_plus_61558
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:09:10.33984+00:00
-- url     : https://prove2.me/submissions/085a3b06-64eb-4fa3-9378-5b435547e9d6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, x ^ 5 + y ^ 5 + z ^ 5 ≥ 3 * (x ^ 3 + y ^ 3 + z ^ 3 - x ^ 2 - y ^ 2 - z ^ 2) + x ^ 2 + y ^ 2 + z ^ 2 ∧ 3 * (x ^ 3 + y ^ 3 + z ^ 3 - x ^ 2 - y ^ 2 - z ^ 2) + x ^ 2 + y ^ 2 + z ^ 2 ≥ x ^ 2 + y ^ 2 + z ^ 2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

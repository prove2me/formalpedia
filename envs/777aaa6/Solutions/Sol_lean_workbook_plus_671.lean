-- Prove2me | solution 1 for lean_workbook_plus_671
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:28.849908+00:00
-- url     : https://prove2.me/submissions/7ab23888-8281-4481-bddc-845c5d17617e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ k : ℝ, k > 0 → ∀ x : ℝ, 1 / k ^ 2 * x ^ 2 + x * (1 / k ^ 4 - 1 - 1 / k ^ 2 - 1 / k ^ 3 - 1 / (k * (k ^ 2 + 1))) + (1 / k ^ 2 + 1 / k ^ 3 - 1 / k ^ 4 - 1 / k) ≤ 0) := by
  push_neg
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

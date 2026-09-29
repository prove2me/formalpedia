-- Prove2me | solution 1 for lean_workbook_plus_44570
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:05:16.095785+00:00
-- url     : https://prove2.me/submissions/b8bf4501-7599-41e5-94f7-84803aabcebf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, 4 * (x + y) * (y + z) * (z + x) ≥ 4 * z * x * (2 * y + z + x) + y * (2 * z + x + y) * (2 * x + y + z)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

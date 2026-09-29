-- Prove2me | solution 1 for lean_workbook_plus_64831
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:13:05.465643+00:00
-- url     : https://prove2.me/submissions/2201d287-1650-48aa-abdd-6b7101fc864e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b : ℝ, (2*a-4)^2 + (2*b-3)^2 > 49) := by
  push_neg
  norm_num at *
  refine ⟨ (    1  /  3  ) , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_32790
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:44.689371+00:00
-- url     : https://prove2.me/submissions/a6a6bdb5-fde3-42aa-8b33-dc30b5350411

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (b : ℤ), b^2 + 4 * (b^2 + 1) = 5 * b^2 + 1) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

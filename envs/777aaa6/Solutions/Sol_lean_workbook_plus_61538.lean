-- Prove2me | solution 1 for lean_workbook_plus_61538
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:06:14.960054+00:00
-- url     : https://prove2.me/submissions/193a4a19-7eb1-4d44-abc2-1a8235cef413

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ,
    x * y * (x - y) ^ 2 + y * z * (y - z) ^ 2 + z * x * (z - x) ^ 2 ≥ 0) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

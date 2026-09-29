-- Prove2me | solution 1 for lean_workbook_plus_61523
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:25.038324+00:00
-- url     : https://prove2.me/submissions/a5924443-d98b-4f5d-8f0a-81572e809ccd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, (x^2*y + y^2*z + z^2*x) * (x*y^2 + y*z^2 + z*x^2) * (x*y + y*z + z*x) ≥ (x*y + y*z + z*x)^4 / 3) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

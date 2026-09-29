-- Prove2me | solution 1 for lean_workbook_plus_58494
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:12:34.900754+00:00
-- url     : https://prove2.me/submissions/8992f490-b3c8-4b58-8217-141bd3b61709

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y : ℝ, 22*x^2 - 4*x + 45*y^2 - 144*y + 32*(y-2)^2 - 140 ≥ 0) := by
  push_neg
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

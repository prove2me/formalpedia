-- Prove2me | solution 1 for lean_workbook_plus_56872
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:00:21.518816+00:00
-- url     : https://prove2.me/submissions/43963cf9-5adb-44f9-9de2-efd551f1bd65

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^3 + b^3 + c^3) * (a * b + b * c + c * a)^2 ≥
    3 * a^2 * b^2 * c^2 * (Real.sqrt a + Real.sqrt b + Real.sqrt c)^2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  2 , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_26033
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:01.564522+00:00
-- url     : https://prove2.me/submissions/c66734f5-aef4-4b3c-92d3-244450fb2255

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (a b : ℝ) (hab : a > b) (hb : b > 0), (a + 1) / (b + 1) ≥ a / b) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *

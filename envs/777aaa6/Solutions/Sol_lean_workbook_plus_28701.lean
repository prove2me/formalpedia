-- Prove2me | solution 1 for lean_workbook_plus_28701
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:07.267167+00:00
-- url     : https://prove2.me/submissions/4499df22-36f8-4235-82ef-271bc9190737

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b : ℝ, (a^3+b^3)*(1+1)*(1+1) ≥ (a+b)^3) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

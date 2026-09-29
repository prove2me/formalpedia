-- Prove2me | solution 1 for lean_workbook_plus_5905
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:08.043056+00:00
-- url     : https://prove2.me/submissions/12fdd1b2-f2b2-45e4-b59c-6524694e0e34

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a ^ 3 + b ^ 3 + c ^ 3 ≥ c * (a ^ 2 + a * b + b ^ 2)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

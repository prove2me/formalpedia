-- Prove2me | solution 1 for lean_workbook_plus_40462
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:09.505645+00:00
-- url     : https://prove2.me/submissions/6b5dde38-de93-418c-b012-68a9a08065cc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (1 / (a ^ 3 + b ^ 2 + c ^ 2) + 1 / (b ^ 3 + c ^ 2 + a ^ 2) + 1 / (c ^ 3 + a ^ 2 + b ^ 2) ≤ 3 / (a ^ 2 + b ^ 2 + c ^ 2))) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *

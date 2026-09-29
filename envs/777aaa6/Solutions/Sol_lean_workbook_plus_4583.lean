-- Prove2me | solution 1 for lean_workbook_plus_4583
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:58.22173+00:00
-- url     : https://prove2.me/submissions/c01f71b8-0256-41d0-ab2d-b1c52647c949

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a ^ 3 * b + b ^ 3 * c + c ^ 3 * a >= a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_49021
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:20.788329+00:00
-- url     : https://prove2.me/submissions/bba73c0b-085c-4634-a989-ab829f9b7baa

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, 3 * a * b * c ≤ a ^ 3 + b ^ 3 + c ^ 3) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

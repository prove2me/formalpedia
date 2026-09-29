-- Prove2me | solution 1 for lean_workbook_plus_17116
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:21.856261+00:00
-- url     : https://prove2.me/submissions/c3850835-5c5d-4e46-a623-558fe15e713c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (1 / Real.sqrt (a ^ 2 - a * b + b ^ 2) + 1 / Real.sqrt (b ^ 2 - b * c + c ^ 2) + 1 / Real.sqrt (c ^ 2 - c * a + a ^ 2)) ^ 2 * (a ^ 2 - a * b + b ^ 2 + b ^ 2 - b * c + c ^ 2 + c ^ 2 - c * a + a ^ 2) ≥ 27) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

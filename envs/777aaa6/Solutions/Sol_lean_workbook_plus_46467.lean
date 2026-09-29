-- Prove2me | solution 1 for lean_workbook_plus_46467
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:44.925811+00:00
-- url     : https://prove2.me/submissions/d5628c41-8bcc-4be5-a2dd-368e95366298

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 + 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 12) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_60349
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:06:19.457533+00:00
-- url     : https://prove2.me/submissions/d0b87fab-270d-4a95-98a2-c3f2b6b94377

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a + b) * (b + c) * (c + a) ≥ (8 / 9) * (a + b + c) * (a * b + b * c + c * a) ∧ (a * b + b * c + c * a) ^ 2 ≥ 3 * a * b * c * (a + b + c)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

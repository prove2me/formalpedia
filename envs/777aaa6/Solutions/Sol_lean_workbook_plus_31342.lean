-- Prove2me | solution 1 for lean_workbook_plus_31342
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:34:29.740358+00:00
-- url     : https://prove2.me/submissions/38a7ef66-1236-4511-8d9d-0fe1ccd753b2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≥ 1 ↔ 2 * (a + b + c + 1) ≥ (a + b) * (a + c) * (b + c))) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

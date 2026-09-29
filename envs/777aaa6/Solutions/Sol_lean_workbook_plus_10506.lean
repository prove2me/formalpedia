-- Prove2me | solution 1 for lean_workbook_plus_10506
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:16:16.673457+00:00
-- url     : https://prove2.me/submissions/a358883f-0bdf-4899-8499-e6d88d87f226

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2/(1 + b * c) + b^2/(1 + c * a) + c^2/(1 + a * b) ≥ 3/4)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_79131
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:32.311711+00:00
-- url     : https://prove2.me/submissions/bdc12c11-cc85-4188-8278-935d6b822bcb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a ^ 5 / (a ^ 4 + b ^ 4) + b ^ 5 / (b ^ 4 + c ^ 4) + c ^ 5 / (c ^ 4 + a ^ 4)) ≥ 1 / 2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

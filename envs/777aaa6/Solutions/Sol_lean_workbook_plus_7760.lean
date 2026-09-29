-- Prove2me | solution 1 for lean_workbook_plus_7760
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:07:46.408321+00:00
-- url     : https://prove2.me/submissions/23051ff2-275e-4722-bf9f-5b1c8b3bb15f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (4 * a + 4 * b + c) * (a / 4 + b / 4 + c) ≥ (a + b + c) ^ 2) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_26914
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:50:35.489897+00:00
-- url     : https://prove2.me/submissions/6ec80edc-1e69-435b-8523-867204e7df2c

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (1 / (a + b) ^ 2 + 1 / (b + c) ^ 2 + 1 / (c + a) ^ 2) ≥ 3 / 4) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

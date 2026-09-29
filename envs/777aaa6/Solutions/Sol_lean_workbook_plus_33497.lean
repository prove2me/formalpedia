-- Prove2me | solution 1 for lean_workbook_plus_33497
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:10:57.41063+00:00
-- url     : https://prove2.me/submissions/51d9d815-1daf-41fa-9ddb-4918f0c8b81d

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 + b^2) / (a + b) + (c^2 + a^2) / (c + a) + (b^2 + c^2) / (b + c) ≥ a + b + c) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

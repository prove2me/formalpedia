-- Prove2me | solution 1 for lean_workbook_plus_3620
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:04:34.913655+00:00
-- url     : https://prove2.me/submissions/bf6d0e95-cc8c-42d8-8806-1c853dbd652b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, 8 * (a + b + c) ^ 3 ≥ 27 * (a + b) * (b + c) * (a + c)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

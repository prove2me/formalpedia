-- Prove2me | solution 1 for lean_workbook_plus_46605
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:14:57.597315+00:00
-- url     : https://prove2.me/submissions/78920c81-d053-42c3-b618-5c19f099d18b

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a + b + c) ^ 2 / (a * b + b * c + a * c) ≥ 3) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

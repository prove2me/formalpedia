-- Prove2me | solution 1 for lean_workbook_plus_10605
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:14.33371+00:00
-- url     : https://prove2.me/submissions/da749d16-f793-45ac-9bb4-28b3c28db493

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 3 * a * b * c ≥ 9) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

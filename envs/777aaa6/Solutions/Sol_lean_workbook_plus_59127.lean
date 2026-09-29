-- Prove2me | solution 1 for lean_workbook_plus_59127
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:13:17.604921+00:00
-- url     : https://prove2.me/submissions/7547e5e0-de8c-4be6-9ae6-22030d08aba0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x1 x2 x3 : ℝ, (1 + x1 ^ 3) * (1 + x2 ^ 3) * (1 + x3 ^ 3) ≥ (1 + x1 * x2 * x3) ^ 3) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

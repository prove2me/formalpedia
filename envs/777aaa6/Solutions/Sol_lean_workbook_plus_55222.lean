-- Prove2me | solution 1 for lean_workbook_plus_55222
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:20:26.695711+00:00
-- url     : https://prove2.me/submissions/02a1ec69-c36b-4f9a-b5ee-0bc276eb45d0

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 4 * (a + b + c) ^ 3  > 27 * (a ^ 3 + b ^ 3 + c ^ 3)) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_65573
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T15:59:07.078162+00:00
-- url     : https://prove2.me/submissions/a3c8cd04-805c-414d-91b5-04f6f4910d44

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c x : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a^4 + b^4 + c^4 = a * b * c * (a + b + c) ↔ a = b ∧ b = c ∧ c = x) := by
  push_neg
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
  refine ⟨ 1 , ?_⟩
  norm_num

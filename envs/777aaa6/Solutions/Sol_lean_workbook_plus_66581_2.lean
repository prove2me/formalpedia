-- Prove2me | solution 2 for lean_workbook_plus_66581
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:07:20.540121+00:00
-- url     : https://prove2.me/submissions/99afdd01-7d6d-44f0-bebc-1ec056933066

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 3 → a * b ^ 2 * (b ^ 2 + 1) + b * c ^ 2 * (c ^ 2 + 1) + c * a ^ 2 * (a ^ 2 + 1) ≤ 6) := by
  push_neg
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *

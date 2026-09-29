-- Prove2me | solution 1 for lean_workbook_plus_59602
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:04:34.872014+00:00
-- url     : https://prove2.me/submissions/84dd5200-76b1-4574-a9b6-726f121a7d24

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℕ, (a * b / (a + b + 2 * c + 1) + b * c / (b + c + 2 * a + 1) + c * a / (c + a + 2 * b + 1) : ℚ) ≤ 3 / 5) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *

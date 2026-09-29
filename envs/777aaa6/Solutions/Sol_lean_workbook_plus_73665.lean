-- Prove2me | solution 1 for lean_workbook_plus_73665
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:28.178536+00:00
-- url     : https://prove2.me/submissions/46e4461a-d6fc-4d17-b156-7366b39c75ce

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, (6 * x + 2 * y + 2 * z) ^ 5 * (5 * y + 5 * z) ^ 4 ≤  1 / 9 * (10 / 3 * (x + y + z)) ^ 9) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

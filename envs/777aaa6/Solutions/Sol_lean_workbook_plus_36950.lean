-- Prove2me | solution 1 for lean_workbook_plus_36950
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:20.075536+00:00
-- url     : https://prove2.me/submissions/4b44fa4d-782c-430b-abd6-47dcc73721f5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 + x + y + z ≥ x ^ 2 + y ^ 2 + z ^ 2 + 3 ∧ x ^ 2 + y ^ 2 + z ^ 2 + 3 ≥ 2 * (x * y + x * z + y * z)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

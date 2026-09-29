-- Prove2me | solution 1 for lean_workbook_plus_38214
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:10:11.534151+00:00
-- url     : https://prove2.me/submissions/debc3cbe-35df-4ea1-bccb-fb62166dfcdc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, 2 * x ^ 6 + 2 * y ^ 6 - y ^ 6 + 3 * x ^ 2 * y ^ 2 * z ^ 2 - 6 * x ^ 3 * z ^ 3 ≥ 0) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

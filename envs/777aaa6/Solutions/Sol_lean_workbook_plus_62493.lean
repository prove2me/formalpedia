-- Prove2me | solution 1 for lean_workbook_plus_62493
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:05:09.110034+00:00
-- url     : https://prove2.me/submissions/26883170-05e7-4150-993d-72a9314e6429

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, 7 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 ≥ (x ^ 5 + y ^ 5 + z ^ 5) * (x + y + z) + 2 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) * (x + y + z) ^ 2) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

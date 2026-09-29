-- Prove2me | solution 1 for lean_workbook_plus_2737
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:08:29.619446+00:00
-- url     : https://prove2.me/submissions/f8cada71-08ec-4f78-906f-e872c13a0788

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, x ^ 4 + y ^ 4 + z ^ 4 + (x ^ 2 + y ^ 2 + z ^ 2) * (x * y + y * z + z * x) ≥ 4 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

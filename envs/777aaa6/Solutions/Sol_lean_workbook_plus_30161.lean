-- Prove2me | solution 1 for lean_workbook_plus_30161
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:16:13.880618+00:00
-- url     : https://prove2.me/submissions/e9bd4dbd-0c06-4362-ba8f-3fa2cdab01c1

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, (x * (x ^ 2 + 4 * x * y) * (x + 3 * y + 7 * z) + y * (y ^ 2 + 4 * y * z) * (y + 3 * z + 7 * x) + z * (4 * x * z + z ^ 2) * (z + 3 * x + 7 * y)) ^ 3 / (x * (x ^ 2 + 4 * x * y) ^ 2 * (x + 3 * y + 7 * z) ^ 3 + y * (y ^ 2 + 4 * y * z) ^ 2 * (y + 3 * z + 7 * x) ^ 3 + z * (4 * x * z + z ^ 2) ^ 2 * (z + 3 * x + 7 * y) ^ 3) ≥ 5 / 9 * (x + y + z) ^ 4) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  2 , ?_⟩
  norm_num at *

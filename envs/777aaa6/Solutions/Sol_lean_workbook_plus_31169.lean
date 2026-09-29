-- Prove2me | solution 1 for lean_workbook_plus_31169
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:04:28.227556+00:00
-- url     : https://prove2.me/submissions/e4dbaf53-bc65-4c7d-9009-2a6e5cca8947

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, (y - z) ^ 2 * (x ^ 2 + x * y + x * z) / ((x + y) * (z + x) * y * z) ≥ 0) := by
  push_neg
  norm_num
  refine ⟨ 1 , ?_⟩
  norm_num
  refine ⟨ -  2 , ?_⟩
  norm_num
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num

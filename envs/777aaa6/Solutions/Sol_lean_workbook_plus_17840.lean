-- Prove2me | solution 1 for lean_workbook_plus_17840
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:00:56.43882+00:00
-- url     : https://prove2.me/submissions/0dd788e9-b0e9-4b5d-89a3-b22f2891f91e

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 + 16 * b * c) / (b^2 + c^2) + (b^2 + 16 * c * a) / (c^2 + a^2) + (c^2 + 16 * a * b) / (a^2 + b^2) ≥ 10) := by
  push_neg
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num

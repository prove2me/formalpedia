-- Prove2me | solution 1 for lean_workbook_plus_49048
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:34:33.8877+00:00
-- url     : https://prove2.me/submissions/ea0fc92a-1493-4f51-a990-6c30283bd627

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, 2 * Real.sqrt (x * (y^29 + z^2007)) ≤ x + y^29 + z^2007) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

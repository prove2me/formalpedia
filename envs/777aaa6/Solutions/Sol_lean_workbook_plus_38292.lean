-- Prove2me | solution 1 for lean_workbook_plus_38292
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:56:52.061896+00:00
-- url     : https://prove2.me/submissions/ea4e241b-2b53-40cf-85a1-c7dad23c576b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ t : ℝ, (1 - 2 * t) * (t - 1 / 3) ^ 2 ≥ 0) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

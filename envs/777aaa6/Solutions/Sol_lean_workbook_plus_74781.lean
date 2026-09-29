-- Prove2me | solution 1 for lean_workbook_plus_74781
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:51:11.517595+00:00
-- url     : https://prove2.me/submissions/49ca0ebf-59fa-425e-9d19-a73c3c293937

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x1 x2 : ℝ, (1 - x1) * (1 - x2) ≥ 1 - (x1 + x2)) := by
  push_neg
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

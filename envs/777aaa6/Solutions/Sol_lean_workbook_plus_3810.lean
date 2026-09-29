-- Prove2me | solution 1 for lean_workbook_plus_3810
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:48:59.176163+00:00
-- url     : https://prove2.me/submissions/f78f929a-7987-42e6-8dc7-d15a6ae577ec

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a : ℝ, (a^3 + 1)^2 ≥ (a^2 + 1) * (a^4 + 1)) := by
  push_neg
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_17318
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:26:44.558309+00:00
-- url     : https://prove2.me/submissions/b23966cd-3415-44d3-b5d9-e2e41611d90c

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a c : ℝ, (1 / a + 2 * Real.sqrt 2 / c) * (1 / a + 2 * Real.sqrt 2 / c) * (a ^ 2 + c ^ 2) ≥ 27) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

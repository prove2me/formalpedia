-- Prove2me | solution 1 for lean_workbook_plus_14972
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:00:22.846866+00:00
-- url     : https://prove2.me/submissions/c87145b0-4d53-46c0-92e6-9ac78fd2ca31

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ z : ℂ, ‖z‖ < 1 / 2 → 2 * ‖z‖ ^ 2 ≤ ‖z‖ ^ 2) := by
  push_neg
  norm_num
  refine ⟨ (    1  /  3  ) , ?_⟩
  norm_num

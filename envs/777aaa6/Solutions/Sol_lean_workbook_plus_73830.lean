-- Prove2me | solution 1 for lean_workbook_plus_73830
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:44:22.473137+00:00
-- url     : https://prove2.me/submissions/894ee4e8-1f29-4488-9765-67ac1b05210e

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, -9 * a ^ 2 * b ^ 2 * c ^ 2 ≥ -a * b * c * (a + b + c)) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

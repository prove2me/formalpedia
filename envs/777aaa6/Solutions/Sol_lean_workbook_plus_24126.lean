-- Prove2me | solution 1 for lean_workbook_plus_24126
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:04:03.253587+00:00
-- url     : https://prove2.me/submissions/0a4533e4-f2c0-43a2-ab77-88bfdfb8bc73

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, x^2 + y^2 + z^2 + 6 ≥ (x + y + z)^2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *

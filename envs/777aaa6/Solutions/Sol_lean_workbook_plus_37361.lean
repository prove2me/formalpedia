-- Prove2me | solution 1 for lean_workbook_plus_37361
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:58:35.132508+00:00
-- url     : https://prove2.me/submissions/85d65d89-b2f6-47e0-8c8b-812dbca8361e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a : ℝ, (a^4 - 3*a^2 + 3) * (a^4 - a^2 + 1) = (a^4 - 2*a^2 + 2)^2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

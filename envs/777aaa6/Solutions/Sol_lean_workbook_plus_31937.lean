-- Prove2me | solution 1 for lean_workbook_plus_31937
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:02:17.437134+00:00
-- url     : https://prove2.me/submissions/35759c7a-798b-49be-a205-4db6a3a743e5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 + 3 * b * c) / (b + c)^2 + (b^2 + 3 * c * a) / (c + a)^2 + (c^2 + 3 * a * b) / (a + b)^2 ≥ 11 / 4 + 2 * a * b * c / (a + b) / (b + c) / (c + a)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_61701
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:11:12.166084+00:00
-- url     : https://prove2.me/submissions/2aa71f28-3117-467d-b6a2-6676ac39bb90

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a / (b + c) + b / (c + a) + c / (a + b) + (a^2 - b^2) * (b^2 - c^2) * (c^2 - a^2) / ((a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2))) ≥ 3 / 2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

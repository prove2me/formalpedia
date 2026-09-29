-- Prove2me | solution 1 for lean_workbook_plus_20761
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:52.147422+00:00
-- url     : https://prove2.me/submissions/36eeeeb6-9c43-4b08-a912-39fa519df482

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ m k z : ℂ,  z = m^2 - 1 → z * (z + 1) * (z + 2) * (z + 3) = (3 * m^2 * k^2 - 3 * m * k)^2 + (3 * m * k^2 + 3 * k * m^2)^2) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

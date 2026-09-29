-- Prove2me | solution 1 for lean_workbook_plus_35983
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:21.96461+00:00
-- url     : https://prove2.me/submissions/e7d6aca7-607a-41e1-ac4e-d4faa2a881eb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ,
    5 * (x^3 + y^3 + z^3) + 19 * (x^2 * y + y^2 * z + z^2 * x) ≥ 30 * x * y * z + 14 * (x * y^2 + y * z^2 + z * x^2)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *

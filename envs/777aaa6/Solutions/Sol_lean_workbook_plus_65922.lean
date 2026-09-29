-- Prove2me | solution 1 for lean_workbook_plus_65922
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:12:34.812791+00:00
-- url     : https://prove2.me/submissions/c60723a4-4dd4-4d88-b5e8-435c603ad592

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ ((-8 : ℝ)^(1/3) = -2) := by
  push_neg
  norm_num at *

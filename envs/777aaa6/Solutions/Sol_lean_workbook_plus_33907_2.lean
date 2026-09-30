-- Prove2me | solution 2 for lean_workbook_plus_33907
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:51.109708+00:00
-- url     : https://prove2.me/submissions/af459a6b-4669-4379-a2f7-aa3c276ba232

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ c : ℝ, (4 / 3 + (4 * c * (2 - c) * (c - 1) ^ 2) / ((c ^ 2 + 2) * ((2 - c) ^ 2 + 2))) ≥ 4 / 3) := by
  push_neg
  refine ⟨(-1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

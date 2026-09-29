-- Prove2me | solution 1 for lean_workbook_plus_25367
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:07.144955+00:00
-- url     : https://prove2.me/submissions/fc6b7e49-e6e1-43a3-a237-345831c4bbc5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (¬∃ (k m n : ℤ), k^2 = m*n*(m^2-n^2) ∧  Int.gcd m n = 1) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

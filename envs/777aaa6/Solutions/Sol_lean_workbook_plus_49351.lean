-- Prove2me | solution 1 for lean_workbook_plus_49351
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:20.8993+00:00
-- url     : https://prove2.me/submissions/10250c3a-a64a-4e4d-a0fe-32721788265e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ n : ℕ, ¬ (∃ m : ℤ, (2^n-1)*(3^n-1) = m^2)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

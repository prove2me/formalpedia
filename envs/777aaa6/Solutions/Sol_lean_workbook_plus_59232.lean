-- Prove2me | solution 1 for lean_workbook_plus_59232
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:13.281785+00:00
-- url     : https://prove2.me/submissions/c343816b-c42b-4a14-8905-fd94cb6eef98

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (n:ℕ) (hn: 1 ≤ n), 9 ∣ 9^n - 1) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

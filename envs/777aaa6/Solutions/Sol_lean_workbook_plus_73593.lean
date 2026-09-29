-- Prove2me | solution 1 for lean_workbook_plus_73593
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:31.000369+00:00
-- url     : https://prove2.me/submissions/dda821a1-b49c-460e-810d-3afd8a07d6ea

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (x Q : ℤ → ℤ) (h₁ : ∀ x, Q x = x * Q x - x * Q x + x * Q x), ∀ x, x^2 * Q (x^2) + x * (x * Q x - x * Q x) = x^2 * (Q x)^2 + 2 * x^2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *

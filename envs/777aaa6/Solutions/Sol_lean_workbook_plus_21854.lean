-- Prove2me | solution 1 for lean_workbook_plus_21854
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:51:15.310176+00:00
-- url     : https://prove2.me/submissions/b203f445-082e-49cf-a17a-65e7735d35d6

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (f : ℝ → ℝ)
    (h₀ : f 0 = 0)
    (h₁ : ∀ x y, f (x + y) ≥ f x + y * f (f x)), False) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

-- Prove2me | solution 1 for lean_workbook_plus_57173
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:53:37.73609+00:00
-- url     : https://prove2.me/submissions/75398d58-ff39-4ee9-b250-3a6d4fcc1f9f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c d : ℝ, a^2 + b^2 + c^2 + d^2 + a * b * c * d + 1 ≥ a * b + a * c + a * d + b * c + b * d + c * d) := by
  push_neg
  refine ⟨(-3), ?_⟩
  refine ⟨(5/2), ?_⟩
  refine ⟨(3), ?_⟩
  refine ⟨(2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

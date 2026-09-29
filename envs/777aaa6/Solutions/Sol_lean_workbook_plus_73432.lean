-- Prove2me | solution 1 for lean_workbook_plus_73432
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:25.478839+00:00
-- url     : https://prove2.me/submissions/571405eb-7133-4217-9d98-3416945b95b9

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
theorem solution : ¬ (∀ (n : ℕ), ∀ (a : ℝ), (a > 0 ∧ a < 1) → ⌊(1 + ⌊(1 + n * a ^ 2)/a⌋)/a⌋ = n) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *

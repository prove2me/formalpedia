-- Prove2me | solution 1 for lean_workbook_plus_1849
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:43.140765+00:00
-- url     : https://prove2.me/submissions/7c5417e0-9945-4737-9d22-46a3dd22b08e

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
theorem solution : ¬ (∀ a b c : ℝ, (9 / 13 * a ^ 4 * b + 1 / 13 * b ^ 4 * c + 3 / 13 * c ^ 4 * a ≥ a ^ 3 * b * c ∧ 6 / 13 * a ^ 4 * b + 5 / 13 * b ^ 4 * c + 2 / 13 * c ^ 4 * a ≥ a ^ 2 * b ^ 2 * c ∧ 5 / 13 * a ^ 4 * c + 6 / 13 * b ^ 4 * a + 2 / 13 * c ^ 4 * b ≥ a ^ 2 * b ^ 2 * c ∧ 9 / 13 * a ^ 4 * c + 3 / 13 * b ^ 4 * a + 1 / 13 * c ^ 4 * b ≥ a ^ 3 * b * c ∧ 2 / 7 * a ^ 3 * c ^ 2 + 4 / 7 * b ^ 3 * a ^ 2 + 1 / 7 * c ^ 3 * b ^ 2 ≥ a ^ 2 * b ^ 2 * c)) := by
  push_neg
  refine ⟨(3/2), ?_⟩
  refine ⟨(-4), ?_⟩
  refine ⟨(-1/3), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

-- Prove2me | solution 1 for lean_workbook_plus_24837
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:58:43.235383+00:00
-- url     : https://prove2.me/submissions/f122611d-758b-4388-9bd7-593772885d42

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
theorem solution : ¬ (∀ n : ℕ, Nat.Prime n → 6 ∣ n^2 - n) := by
  push_neg
  refine ⟨(2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]

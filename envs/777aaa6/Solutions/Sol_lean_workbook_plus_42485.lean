-- Prove2me | solution 1 for lean_workbook_plus_42485
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:56:52.388887+00:00
-- url     : https://prove2.me/submissions/ad56cf4e-e94a-4152-8b7b-d3cc7b8fb86f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ m n : ℕ, m > n ∧ Nat.gcd (2 ^ n) (2 ^ n - 1) = 1 → (2 ^ n - 1) ∣ (2 ^ (m - n) + 1)) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *

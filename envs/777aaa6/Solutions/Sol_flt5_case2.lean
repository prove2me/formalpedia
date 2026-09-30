-- Prove2me | solution 1 for flt5_case2
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:06:14.853931+00:00
-- url     : https://prove2.me/submissions/a7bf2b0e-825c-4e1d-9db9-f63a54508206

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℤ, a ^ 5 + b ^ 5 = c ^ 5 →
    Int.gcd a b = 1 → (5 : ℤ) ∣ c → False) := by
  intro h
  exact h 1 (-1) 0 (by norm_num) (by norm_num) (by norm_num)

#print axioms solution

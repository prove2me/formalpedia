-- Prove2me | solution 1 for lean_workbook_plus_66512
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:30:59.385149+00:00
-- url     : https://prove2.me/submissions/b6efeb3b-ec3d-4361-926e-4a6bffd2a510

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (n k : ℕ) (h₁ : 1 ≤ k) (h₂ : k ≤ 2 * n) :
    k * (2 * n + 1 - k) ≤ n * (n + 1) := by
  have hbound : k ≤ 2 * n + 1 := by omega
  have hi : (k : ℤ) * (2 * n + 1 - k) ≤ n * (n + 1) := by
    by_cases hk : k ≤ n
    · have hp := mul_nonneg (by omega : 0 ≤ (n : ℤ) - k)
        (by omega : 0 ≤ (n : ℤ) + 1 - k)
      nlinarith
    · have hp := mul_nonneg (by omega : 0 ≤ (k : ℤ) - n)
        (by omega : 0 ≤ (k : ℤ) - n - 1)
      nlinarith
  exact_mod_cast (show (k : ℤ) * ((2 * n + 1 - k : ℕ) : ℤ) ≤
      (n : ℤ) * (n + 1) by
    simpa only [Nat.cast_sub hbound, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hi)

#print axioms solution

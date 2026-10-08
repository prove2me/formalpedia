-- Prove2me | solution 2 for WeakGoldbach.three_odd_primes_ge_10pow27
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T19:58:24.526262+00:00
-- url     : https://prove2.me/submissions/2028f755-6f31-47ac-b709-791a5bd9e99c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_three_odd_primes_10pow27_to_exp3100
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_exp3100

set_option autoImplicit false

/-- Same range split as `ternary_goldbach_helfgott_above_10pow27`, with binders in graph order. -/
theorem solution (n : ℕ) (hn : 10 ^ 27 ≤ n) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  by_cases h : (n : ℝ) < Real.exp 3100
  · exact WeakGoldbach.three_odd_primes_10pow27_to_exp3100 n hn h hodd
  · have hge : Real.exp 3100 ≤ (n : ℝ) := not_lt.mp h
    exact WeakGoldbach.three_odd_primes_ge_exp3100 n hge hodd

#print axioms solution

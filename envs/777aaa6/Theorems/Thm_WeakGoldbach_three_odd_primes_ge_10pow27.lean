-- Prove2me | Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27
-- name    : WeakGoldbach.three_odd_primes_ge_10pow27
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T04:29:03.829731+00:00
-- url     : https://prove2.me/theorems/3a41da7a-027f-40ff-a77e-c35bf4ce0981
-- title:
--   Ternary Goldbach with odd primes for $n \ge 10^{27}$
-- statement:
--   For every odd natural number $n \ge 10^{27}$ there exist **odd** primes $p, q, r$ with $n = p + q + r$.
--
--   This is the analytic half of the ternary Goldbach theorem: Helfgott's circle-method argument proves every odd $n \ge 10^{27}$ is a sum of three odd primes.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748

import Mathlib

namespace WeakGoldbach

theorem three_odd_primes_ge_10pow27 (n : ℕ)
    (hn : 10 ^ 27 ≤ n) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  sorry

end WeakGoldbach

-- Prove2me | Theorems.Thm_WeakGoldbach_three_odd_primes_ge_exp3100
-- name    : WeakGoldbach.three_odd_primes_ge_exp3100
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T14:51:32.84696+00:00
-- url     : https://prove2.me/theorems/ae818708-c215-48ef-81d9-453b080ed1e5
-- title:
--   All-odd ternary Goldbach for $n \ge e^{3100}$
-- statement:
--   For every odd natural number $n \ge e^{3100}$ there exist **odd** primes $p, q, r$ with $n = p + q + r$.
--
--   This is the Liu–Wang effective-Vinogradov regime, strengthened to odd summands: their estimate shows the weighted representation count is positive (in fact $\gg n^2$), while representations involving the prime $2$ are of the shape $\{2,2,n-4\}$ and contribute only $O(\log^2 n)$, so an all-odd representation must exist.
-- source:
--   M.-C. Liu and T. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105 (2002), strengthened to odd summands by the weighted-count argument

import Mathlib

namespace WeakGoldbach

theorem three_odd_primes_ge_exp3100 (n : ℕ)
    (hn : Real.exp 3100 ≤ (n : ℝ)) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  sorry

end WeakGoldbach

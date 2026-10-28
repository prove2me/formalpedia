-- Prove2me | Theorems.Thm_gpy_sum_mu_mul_prod
-- name    : gpy_sum_mu_mul_prod
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T17:10:02.799869+00:00
-- url     : https://prove2.me/theorems/ded292ad-9e57-4c75-afa4-ba70f121922a
-- title:
--   Mobius-weighted divisor sum as Euler product over prime factors (squarefree case)
-- statement:
--   Let f be a multiplicative arithmetic function and n a squarefree natural number. Then the sum over divisors d of n of mu(d) * f(d) equals the product over the prime factors p of n of (1 - f(p)). This is the finite local-factor identity at one prime set: for squarefree n, the Mobius-weighted divisor sum factors over the primes dividing n.
-- source:
--   GPY monomial-sum evaluation: the finite local-factor identity for multiplicative arithmetic functions at squarefree n

import Mathlib
open Classical

theorem gpy_sum_mu_mul_prod {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * f d
      = ∏ p ∈ n.primeFactors, (1 - f p) := by sorry

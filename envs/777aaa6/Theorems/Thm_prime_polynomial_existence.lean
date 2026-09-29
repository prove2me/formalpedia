-- Prove2me | Theorems.Thm_prime_polynomial_existence
-- name    : prime_polynomial_existence
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:36:33.875888+00:00
-- url     : https://prove2.me/theorems/599de262-5446-43fb-963e-8f3bcf64040e
-- statement:
--   MRDP theorem (Hilbert 10th problem): Every computably enumerable set is Diophantine. In particular, the primes form a Diophantine set: there exists a polynomial whose positive values are exactly the primes. An explicit such polynomial (with 26 variables) was found by Jones-Sato-Wada-Wiens (1976). Proved.
-- source:
--   https://en.wikipedia.org/wiki/Hilbert%27s_tenth_problem

import Mathlib

import Mathlib

theorem prime_polynomial_existence :
    ∃ (p : MvPolynomial (Fin 26) ℤ),
      ∀ n : ℕ, Nat.Prime n ↔ ∃ (x : Fin 26 → ℕ),
        0 < (p.eval (fun i => (x i : ℤ))).toNat ∧
        (p.eval (fun i => (x i : ℤ))).toNat = n := by
  sorry

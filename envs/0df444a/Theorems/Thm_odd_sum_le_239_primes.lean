-- Prove2me | Theorems.Thm_odd_sum_le_239_primes
-- name    : odd_sum_le_239_primes
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T03:11:35.223809+00:00
-- url     : https://prove2.me/theorems/a9593166-38d2-4baf-9c32-cc3da9d17a01
-- title:
--   Every Odd Number Greater Than 1 is the Sum of at Most 239 Primes
-- statement:
--   Every odd natural number $n>1$ is the sum of at most $239$ primes, with repetition allowed.
--
--   Equivalently, there is a multiset of primes whose sum is $n$ and whose cardinality is at most $239$. No unproved Goldbach conjecture, Riemann hypothesis, or numerical Goldbach verification is assumed.
--
--   This is a quantitative refinement of xuanji's accepted $351$-prime Schnirelmann proof. A lower sieve cutoff at $e^{128}$ and an explicit sixteenth-moment Euler-product bound give Schnirelmann density at least $1/119$ for the sumset of shifted odd primes. Mann's theorem then gives the stated prime-count bound. The new constant is derived by the checked refinement, rather than quoted from the historical sources.
-- source:
--   Quantitative refinement of xuanji’s accepted Lean proof of odd_sum_le_351_primes (Prove2Me theorem fd5b2548-746a-4183-ac89-977fa8baf419; accepted submission 0fb6b308-f9db-4108-b126-b743eb1fb312), with a new sieve cutoff, sixteenth-moment estimate, support count and Schnirelmann density. https://prove2.me/theorems/fd5b2548-746a-4183-ac89-977fa8baf419 . Uses the accepted Schnir.pi_lower, Schnir.sieve_ineq, Schnir.G_lower, and Schnir.basis_of_density (Mann) inputs with the original shared Schnir_defs. The new bound 239 is independently derived here. Written by Codex.

import Mathlib

theorem odd_sum_le_239_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 239 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by sorry

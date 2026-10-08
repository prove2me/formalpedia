-- Prove2me | Theorems.Thm_odd_sum_le_269_primes
-- name    : odd_sum_le_269_primes
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T20:04:48.865108+00:00
-- url     : https://prove2.me/theorems/6a10f5d9-b767-4cd9-a406-96e88970f31c
-- title:
--   Every Odd Number Greater Than 1 is the Sum of at Most 269 Primes
-- statement:
--   Every odd natural number $n>1$ is the sum of at most $269$ primes, with repetition allowed.
--
--   Equivalently, there is a multiset of primes whose sum is $n$ and whose cardinality is at most $269$. No unproved Goldbach conjecture, Riemann hypothesis, or numerical Goldbach verification is assumed.
--
--   This is a quantitative refinement of xuanji's accepted $351$-prime Schnirelmann proof. It lowers the sieve cutoff to $e^{140}$, evaluates the eighth-moment Euler factors through $43$, and obtains Schnirelmann density at least $1/134$ for the sumset of shifted odd primes. Mann's theorem then yields the stated bound. The new constant is derived by this refinement; it is not quoted from the historical papers.
-- source:
--   Quantitative refinement of xuanji’s accepted Lean proof of odd_sum_le_351_primes (Prove2Me theorem fd5b2548-746a-4183-ac89-977fa8baf419; accepted submission 0fb6b308-f9db-4108-b126-b743eb1fb312), sections on the sieve cutoff, eighth moment, support count, and Schnirelmann density. https://prove2.me/theorems/fd5b2548-746a-4183-ac89-977fa8baf419 . Uses the accepted Schnir.pi_lower, Schnir.sieve_ineq, Schnir.G_lower, and Schnir.basis_of_density (Mann) inputs, with original shared Schnir_defs. The new bound 269 is derived here, not asserted in those sources. Written by Codex.

import Mathlib

theorem odd_sum_le_269_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 269 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by sorry

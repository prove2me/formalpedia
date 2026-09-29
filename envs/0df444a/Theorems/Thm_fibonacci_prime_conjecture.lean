-- Prove2me | Theorems.Thm_fibonacci_prime_conjecture
-- name    : fibonacci_prime_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T21:08:29.437907+00:00
-- url     : https://prove2.me/theorems/d784b789-cd7d-41cc-9757-7efb751d99b3
-- statement:
--   Fibonacci prime conjecture: Are there infinitely many Fibonacci primes? The known Fibonacci primes occur at indices n = 3, 4, 5, 7, 11, 13, 17, 23, 29, 43, 47, 83, 131, ... As of 2024, the largest known is Fib(3340367) with over 600,000 digits. No proof that infinitely many exist.
-- source:
--   https://en.wikipedia.org/wiki/Fibonacci_prime

import Mathlib

import Mathlib

theorem fibonacci_prime_conjecture :
    {n : ℕ | Nat.Prime (Nat.fib n)}.Infinite := by
  sorry

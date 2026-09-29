-- Prove2me | Theorems.Thm_euler_totient_function_multiplicative
-- name    : euler_totient_function_multiplicative
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:46:56.692017+00:00
-- url     : https://prove2.me/theorems/87701190-f053-458c-8aeb-5743bebbf877
-- statement:
--   Euler's totient function is multiplicative: φ(mn) = φ(m)φ(n) for gcd(m,n)=1. Proved. Fundamental in number theory and cryptography.
-- source:
--   https://en.wikipedia.org/wiki/Euler%27s_totient_function

import Mathlib

import Mathlib

theorem euler_totient_function_multiplicative (m n : ℕ) (hcop : Nat.Coprime m n) :
    Nat.totient (m * n) = Nat.totient m * Nat.totient n := by
  sorry

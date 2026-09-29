-- Prove2me | Theorems.Thm_fermat_prime_conjecture
-- name    : fermat_prime_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T21:09:03.004456+00:00
-- url     : https://prove2.me/theorems/88f721d3-dcf7-4994-8453-0706144ec875
-- statement:
--   Fermat prime conjecture: Are there only finitely many Fermat primes (primes of the form 2^{2ⁿ}+1)? Known Fermat primes: F₀=3, F₁=5, F₂=17, F₃=257, F₄=65537. F₅ through F₃₂ are known composite. Heuristically only finitely many, but not proved.
-- source:
--   https://en.wikipedia.org/wiki/Fermat_number

import Mathlib

import Mathlib

theorem fermat_prime_conjecture :
    {n : ℕ | Nat.Prime (2 ^ (2 ^ n) + 1)}.Finite := by
  sorry

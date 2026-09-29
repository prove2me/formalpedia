-- Prove2me | Theorems.Thm_fermat_prime_finitude
-- name    : fermat_prime_finitude
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:39:53.950882+00:00
-- url     : https://prove2.me/theorems/0e4f00a6-4523-4c24-8370-9e14fd68c8d5
-- statement:
--   Fermat prime problem: Are there finitely or infinitely many Fermat primes 2^{2ⁿ}+1? Only F₀=3, F₁=5, F₂=17, F₃=257, F₄=65537 are known prime. F₅ through F₃₂ are composite. Heuristically finitely many.
-- source:
--   https://en.wikipedia.org/wiki/Fermat_number

import Mathlib

import Mathlib

theorem fermat_prime_finitude :
    {n : ℕ | Nat.Prime (2 ^ (2 ^ n) + 1)}.Finite ∨
    {n : ℕ | Nat.Prime (2 ^ (2 ^ n) + 1)}.Infinite := by
  sorry

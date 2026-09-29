-- Prove2me | Theorems.Thm_collatz_conjecture
-- name    : collatz_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:25:20.202667+00:00
-- url     : https://prove2.me/theorems/6911c758-1598-4425-a467-be9d35228184
-- statement:
--   **Collatz Conjecture** (3n+1 Problem): Starting from any positive integer $n$, the iteration $f(n) = n/2$ (if $n$ even) or $f(n) = 3n+1$ (if $n$ odd) eventually reaches 1.
--
--   Example: $6 \to 3 \to 10 \to 5 \to 16 \to 8 \to 4 \to 2 \to 1$.
--
--   Proposed by Lothar Collatz in 1937. Verified for all integers up to $2^{68}$. Tao (2019) proved almost all orbits reach arbitrarily small values. Erdős said 'Mathematics is not yet ready for such problems'.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture

import Mathlib

def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

theorem collatz_conjecture (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, collatzStep^[m] n = 1 := by
  sorry

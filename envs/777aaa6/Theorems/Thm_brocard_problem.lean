-- Prove2me | Theorems.Thm_brocard_problem
-- name    : brocard_problem
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:26:46.167354+00:00
-- url     : https://prove2.me/theorems/440afc85-a6a4-4a08-89f3-4e6ffa7b613c
-- statement:
--   **Brocard’s Problem**: The only natural numbers $n$ for which $n! + 1$ is a perfect square are $n = 4$, $n = 5$, and $n = 7$.
--
--   Known solutions: $4! + 1 = 25 = 5^2$, $5! + 1 = 121 = 11^2$, $7! + 1 = 5041 = 71^2$.
--
--   Proposed by Henri Brocard (1876), rediscovered by Ramanujan (1913). Verified computationally for $n \leq 10^9$. Granville showed the ABC conjecture implies only finitely many solutions.
-- source:
--   https://en.wikipedia.org/wiki/Brocard%27s_problem

import Mathlib

theorem brocard_problem :
    ∀ n : ℕ, (∃ m : ℕ, Nat.factorial n + 1 = m ^ 2) ↔ n = 4 ∨ n = 5 ∨ n = 7 := by
  sorry

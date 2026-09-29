-- Prove2me | Theorems.Thm_landau_fourth_problem
-- name    : landau_fourth_problem
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:26:07.775241+00:00
-- url     : https://prove2.me/theorems/deb1eedd-3efa-4840-8eb4-7f478ca40b42
-- statement:
--   **Landau's Fourth Problem**: There are infinitely many primes of the form $n^2 + 1$.
--
--   Known examples: $2 = 1^2+1$, $5 = 2^2+1$, $17 = 4^2+1$, $37 = 6^2+1$, $101 = 10^2+1$, ...
--
--   One of Landau's four problems (1912). Iwaniec (1978) proved infinitely many integers $n^2+1$ have at most 2 prime factors. The Hardy–Littlewood conjecture predicts asymptotically $\sim C\sqrt{x}/\log x$ such primes up to $x$.
-- source:
--   https://en.wikipedia.org/wiki/Landau%27s_problems

import Mathlib

theorem landau_fourth_problem :
    {p : ℕ | Nat.Prime p ∧ ∃ n : ℕ, p = n ^ 2 + 1}.Infinite := by
  sorry

-- Prove2me | Theorems.Thm_collatz_iterate_pos
-- name    : collatz_iterate_pos
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T03:52:34.757501+00:00
-- url     : https://prove2.me/theorems/2e9d9354-f3df-4c16-b99e-f7326b20615a
-- title:
--   Positivity is preserved along Collatz orbits
-- statement:
--   Let $C$ be the Collatz step map on $\mathbb{N}$, so that $C(n)=n/2$ for even $n$ (natural-number division) and $C(n)=3n+1$ for odd $n$. Then the set of positive integers is invariant under $C$: for every $m \ge 0$ and every $n > 0$,
--
--   $$C^{m}(n) > 0 .$$
--
--   The statement is needed because $C$ is defined as a total function on $\mathbb{N}$ with $C(0)=0$, so $0$ is a fixed point lying outside the conjecture's scope. Every argument that follows an orbit and then restarts the analysis at a later point of that orbit must know that the later point is again a legitimate starting value; this lemma supplies exactly that. The proof is an induction on $m$ using the one-step fact that a positive even number is at least $2$, so halving it leaves a positive number, while $3n+1$ is positive outright.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_collatzStepMap

theorem collatz_iterate_pos (m n : ℕ) (hn : 0 < n) : 0 < collatzStep^[m] n := by
  sorry

-- Prove2me | Theorems.Thm_collatz_descent_even
-- name    : collatz_descent_even
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T03:52:36.147683+00:00
-- url     : https://prove2.me/theorems/2721a59b-a3df-45ca-9136-efec5b2360be
-- title:
--   A positive even number decreases in one Collatz step
-- statement:
--   Let $C$ denote the Collatz step map. If $n$ is a positive even integer then one step already decreases it:
--
--   $$C(n) = \frac{n}{2} < n .$$
--
--   This is the trivial half of the descent analysis of the Collatz map, isolated here because it is the base case of the residue-class split modulo $4$: even starting values need no further argument, and the whole difficulty of proving that every orbit eventually drops below its starting point is concentrated in the odd residue classes. Positivity is essential, since $C(0)=0$ is not smaller than $0$.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_collatzStepMap

theorem collatz_descent_even (n : ℕ) (hn : 0 < n) (he : Even n) : collatzStep n < n := by
  sorry

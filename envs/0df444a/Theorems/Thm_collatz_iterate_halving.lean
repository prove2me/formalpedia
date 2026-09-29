-- Prove2me | Theorems.Thm_collatz_iterate_halving
-- name    : collatz_iterate_halving
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:27:16.936699+00:00
-- url     : https://prove2.me/theorems/29fec3ff-8c6b-4264-9525-f1dc50fb00b8
-- title:
--   $k$ Collatz steps divide out a factor $2^{k}$
-- statement:
--   Let $C$ be the Collatz step map. If $2^{k}$ divides $x$, then the first $k$ steps of the Collatz orbit of $x$ are all halvings, and together they divide out the whole factor:
--
--   $$2^{k} \mid x \quad \Longrightarrow \quad C^{k}(x) = \frac{x}{2^{k}} .$$
--
--   The content is that divisibility by $2^{k}$ propagates: if $2^{k+1} \mid x$ then $x$ is even, so the first step is a halving, and the result is divisible by $2^{k}$, so the induction continues. No positivity hypothesis is needed, since $x = 0$ gives $C^{k}(0) = 0$ on both sides.
--
--   The lemma is the exact bridge between the classical Collatz map and the accelerated map: writing $3n+1 = 2^{v} \cdot m$ with $m$ odd, it says that the run of halvings following an ascending step is executed in one identity rather than step by step.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 2 (the function T and its relation to the Collatz map), https://websites.umich.edu/~lagarias/3x%2B1.html; Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Mathlib
import Definitions.Def_collatzStepMap

theorem collatz_iterate_halving (k x : ℕ) (h : 2 ^ k ∣ x) :
    collatzStep^[k] x = x / 2 ^ k := by
  sorry

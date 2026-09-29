-- Prove2me | Theorems.Thm_collatz_descent_of_syracuse_descent
-- name    : collatz_descent_of_syracuse_descent
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:27:23.831069+00:00
-- url     : https://prove2.me/theorems/1cb4e4cc-13e8-4004-8fc0-0849c0103a6d
-- title:
--   Syracuse descent implies Collatz descent
-- statement:
--   Let $C$ be the Collatz step map and $T$ the Syracuse map. For odd $n$, descent under the accelerated map implies descent under the classical map:
--
--   $$n \text{ odd}, \quad \exists t : T^{t}(n) < n \qquad \Longrightarrow \qquad \exists m : C^{m}(n) < n .$$
--
--   The implication is immediate from the fact that the $T$-orbit of an odd $n$ is a subsequence of its $C$-orbit: the very point $T^{t}(n)$ that witnesses accelerated descent is itself some $C^{M}(n)$, and it is already below $n$.
--
--   The direction proved here is the one needed to attack the Collatz descent problem: it licenses replacing the classical map by the accelerated one on any class of odd starting values, which is what the standard quantitative arguments do. The converse also holds but is not asserted.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 2 (the function T and its relation to the Collatz map), https://websites.umich.edu/~lagarias/3x%2B1.html; Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Mathlib
import Definitions.Def_collatzStepMap
import Definitions.Def_syracuseStep

theorem collatz_descent_of_syracuse_descent (n : ℕ) (hn : ¬ Even n)
    (h : ∃ t : ℕ, syracuseStep^[t] n < n) : ∃ m : ℕ, collatzStep^[m] n < n := by
  sorry

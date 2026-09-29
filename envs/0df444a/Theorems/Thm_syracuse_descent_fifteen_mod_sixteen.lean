-- Prove2me | Theorems.Thm_syracuse_descent_fifteen_mod_sixteen
-- name    : syracuse_descent_fifteen_mod_sixteen
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:27:27.767446+00:00
-- url     : https://prove2.me/theorems/8c399870-0530-4747-94e9-5fb0717268d6
-- title:
--   Syracuse descent for $n \equiv 15 \pmod{16}$
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map. The assertion is that every $n \equiv 15 \pmod{16}$ has a finite accelerated stopping time:
--
--   $$\exists t \in \mathbb{N} : \quad T^{t}(n) < n .$$
--
--   This statement is **open**, and it is the most resistant of the classes left by the refinement of the Collatz descent problem modulo $32$: for $n = 16j+15$ the classical map ascends for four of its first eight steps, accumulating a multiplier $3^{4}/2^{4} = 81/16$. In accelerated form the same obstruction appears as a run of $T$-steps with $v_2(3n+1) = 1$, each multiplying by $3/2$.
--
--   The statement covers the classes $15$ and $31$ modulo $32$, and implies its classical counterpart because the $T$-orbit of an odd $n$ is a subsequence of its $C$-orbit.
--
--   **Formalization Note.** No positivity or oddness hypothesis is needed: $n \equiv 15 \pmod{16}$ forces $n \ge 15$ and $n$ odd. The index $t$ is unconstrained, but $t = 0$ can never witness the conclusion since $n < n$ is false.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 2 (the function T and its relation to the Collatz map), https://websites.umich.edu/~lagarias/3x%2B1.html; Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descent_fifteen_mod_sixteen (n : ℕ) (h : n % 16 = 15) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by
  sorry

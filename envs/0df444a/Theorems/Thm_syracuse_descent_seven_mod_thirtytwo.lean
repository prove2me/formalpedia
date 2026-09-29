-- Prove2me | Theorems.Thm_syracuse_descent_seven_mod_thirtytwo
-- name    : syracuse_descent_seven_mod_thirtytwo
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:27:16.059718+00:00
-- url     : https://prove2.me/theorems/61254560-1a35-4672-a245-0c5418b7a2e9
-- title:
--   Syracuse descent for $n \equiv 7 \pmod{32}$
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map. The assertion is that every $n \equiv 7 \pmod{32}$ has a finite accelerated stopping time:
--
--   $$\exists t \in \mathbb{N} : \quad T^{t}(n) < n .$$
--
--   This statement is **open**. It is the accelerated form of one of the three residue classes left open by the refinement of the Collatz descent problem modulo $32$, and it implies its classical counterpart because the $T$-orbit of an odd $n$ is a subsequence of its $C$-orbit.
--
--   The accelerated form is the one in which the quantitative theory operates: each $T$-step multiplies by $3/2^{v}$ with $v \ge 1$, giving expected multiplier $3/4 < 1$ under the natural heuristic, whereas the classical map alternates growth and contraction. Terras's density theorem and Tao's almost-all result are both statements about $T$.
--
--   **Formalization Note.** No positivity or oddness hypothesis is needed: $n \equiv 7 \pmod{32}$ forces $n \ge 7$ and $n$ odd. The index $t$ is unconstrained, but $t = 0$ can never witness the conclusion since $n < n$ is false.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 2 (the function T and its relation to the Collatz map), https://websites.umich.edu/~lagarias/3x%2B1.html; Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descent_seven_mod_thirtytwo (n : ℕ) (h : n % 32 = 7) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by
  sorry

-- Prove2me | Theorems.Thm_collatz_descent_three_mod_sixteen
-- name    : collatz_descent_three_mod_sixteen
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:14:50.118401+00:00
-- url     : https://prove2.me/theorems/1ab8bc12-cd34-45b9-8726-8a0e58d4d3a5
-- title:
--   Six Collatz steps decrease every $n \equiv 3 \pmod{16}$
-- statement:
--   Let $C$ denote the Collatz step map. Every $n \equiv 3 \pmod{16}$ drops below its starting value after exactly six steps:
--
--   $$n = 16j + 3 \quad \Longrightarrow \quad C^{6}(n) = 9j + 2 < n .$$
--
--   The residue $3$ modulo $16$ fixes the parity of the first six iterates, so the six steps compose into a single affine map. Explicitly the orbit is
--
--   $$16j+3 \ \to\ 48j+10 \ \to\ 24j+5 \ \to\ 72j+16 \ \to\ 36j+8 \ \to\ 18j+4 \ \to\ 9j+2 ,$$
--
--   and $9j + 2 < 16j + 3$ holds for every $j \ge 0$, with no lower bound on $n$ required. The smallest instance is $n = 3$, whose orbit $3, 10, 5, 16, 8, 4, 2$ reaches $2 < 3$.
--
--   This is one class of the residue refinement of the Collatz descent problem: the class $3 \bmod 4$, which the modulo $4$ analysis leaves open, splits modulo $32$ into eight classes, of which four admit a uniform bounded descent. This is the first of them.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, https://websites.umich.edu/~lagarias/3x%2B1.html, Section 2 (stopping time is determined by n mod 2^k; the Terras-Everett analysis of coefficient stopping time). Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Mathlib
import Definitions.Def_collatzStepMap

theorem collatz_descent_three_mod_sixteen (n : ℕ) (h : n % 16 = 3) :
    ∃ m : ℕ, collatzStep^[m] n < n := by
  sorry

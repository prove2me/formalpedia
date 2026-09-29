-- Prove2me | Theorems.Thm_collatz_descent_twentythree_mod_thirtytwo
-- name    : collatz_descent_twentythree_mod_thirtytwo
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:14:51.578573+00:00
-- url     : https://prove2.me/theorems/7c8652d7-1136-405d-b764-79897cf70a4f
-- title:
--   Eight Collatz steps decrease every $n \equiv 23 \pmod{32}$
-- statement:
--   Let $C$ denote the Collatz step map. Every $n \equiv 23 \pmod{32}$ drops below its starting value after exactly eight steps:
--
--   $$n = 32j + 23 \quad \Longrightarrow \quad C^{8}(n) = 27j + 20 < n .$$
--
--   The residue $23$ modulo $32$ fixes the parity of the first eight iterates. The orbit is
--
--   $$32j+23 \to 96j+70 \to 48j+35 \to 144j+106 \to 72j+53 \to 216j+160 \to 108j+80 \to 54j+40 \to 27j+20 ,$$
--
--   again three ascending steps against five halvings, so the multiplier is $27/32 < 1$ and $27j + 20 < 32j + 23$ for every $j \ge 0$. The smallest instance is $n = 23$, whose orbit $23, 70, 35, 106, 53, 160, 80, 40, 20$ reaches $20 < 23$.
--
--   This is one of the four residue classes modulo $32$ inside $3 \bmod 4$ that admit a uniform bounded descent.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, https://websites.umich.edu/~lagarias/3x%2B1.html, Section 2 (stopping time is determined by n mod 2^k; the Terras-Everett analysis of coefficient stopping time). Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Mathlib
import Definitions.Def_collatzStepMap

theorem collatz_descent_twentythree_mod_thirtytwo (n : ℕ) (h : n % 32 = 23) :
    ∃ m : ℕ, collatzStep^[m] n < n := by
  sorry

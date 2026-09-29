-- Prove2me | Theorems.Thm_collatz_descent_eleven_mod_thirtytwo
-- name    : collatz_descent_eleven_mod_thirtytwo
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:14:48.424627+00:00
-- url     : https://prove2.me/theorems/250a7e02-4975-4ebf-a11f-98751701c063
-- title:
--   Eight Collatz steps decrease every $n \equiv 11 \pmod{32}$
-- statement:
--   Let $C$ denote the Collatz step map. Every $n \equiv 11 \pmod{32}$ drops below its starting value after exactly eight steps:
--
--   $$n = 32j + 11 \quad \Longrightarrow \quad C^{8}(n) = 27j + 10 < n .$$
--
--   The residue $11$ modulo $32$ fixes the parity of the first eight iterates, which compose into a single affine map. The orbit is
--
--   $$32j+11 \to 96j+34 \to 48j+17 \to 144j+52 \to 72j+26 \to 36j+13 \to 108j+40 \to 54j+20 \to 27j+10 ,$$
--
--   with three ascending steps and five halvings, so the accumulated multiplier is $3^{3}/2^{5} = 27/32 < 1$; the inequality $27j + 10 < 32j + 11$ then holds for every $j \ge 0$. The smallest instance is $n = 11$, whose orbit $11, 34, 17, 52, 26, 13, 40, 20, 10$ reaches $10 < 11$.
--
--   This is one of the four residue classes modulo $32$ inside $3 \bmod 4$ that admit a uniform bounded descent.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, https://websites.umich.edu/~lagarias/3x%2B1.html, Section 2 (stopping time is determined by n mod 2^k; the Terras-Everett analysis of coefficient stopping time). Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Mathlib
import Definitions.Def_collatzStepMap

theorem collatz_descent_eleven_mod_thirtytwo (n : ℕ) (h : n % 32 = 11) :
    ∃ m : ℕ, collatzStep^[m] n < n := by
  sorry

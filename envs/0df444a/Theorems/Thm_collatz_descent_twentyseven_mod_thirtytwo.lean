-- Prove2me | Theorems.Thm_collatz_descent_twentyseven_mod_thirtytwo
-- name    : collatz_descent_twentyseven_mod_thirtytwo
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:14:53.35672+00:00
-- url     : https://prove2.me/theorems/355d18c5-2ad1-4ace-9cc3-078f0cc4096c
-- title:
--   Collatz descent for $n \equiv 27 \pmod{32}$
-- statement:
--   Let $C$ denote the Collatz step map. The assertion is that every $n \equiv 27 \pmod{32}$ has a finite stopping time:
--
--   $$\exists m \in \mathbb{N} : \quad C^{m}(n) < n .$$
--
--   This class is **open**. Writing $n = 32j + 27$, the parity-determined initial segment ends above the starting value: the accumulated multiplier exceeds $1$ before the parity of the next iterate ceases to be determined by the residue, so no bounded number of steps settles the class, and refining the modulus splits it further without terminating.
--
--   The statement is one of four open classes modulo $32$ left by the residue refinement of the Collatz descent problem; the other three are $7 \bmod 32$ and $15 \bmod 16$. Together they carry the whole remaining difficulty of the descent principle, and hence of the Collatz conjecture.
--
--   **Formalization Note.** No positivity hypothesis is needed: $n \equiv 27 \pmod{32}$ forces $n \ge 27$. The index $m$ is unconstrained, but $m = 0$ can never witness the conclusion since $n < n$ is false.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, https://websites.umich.edu/~lagarias/3x%2B1.html, Section 2 (stopping time is determined by n mod 2^k; the Terras-Everett analysis of coefficient stopping time). Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Mathlib
import Definitions.Def_collatzStepMap

theorem collatz_descent_twentyseven_mod_thirtytwo (n : ℕ) (h : n % 32 = 27) :
    ∃ m : ℕ, collatzStep^[m] n < n := by
  sorry

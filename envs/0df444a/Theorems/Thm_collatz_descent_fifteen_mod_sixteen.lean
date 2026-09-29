-- Prove2me | Theorems.Thm_collatz_descent_fifteen_mod_sixteen
-- name    : collatz_descent_fifteen_mod_sixteen
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:14:55.336326+00:00
-- url     : https://prove2.me/theorems/64511278-09d4-4d70-9066-cefb09257ac8
-- title:
--   Collatz descent for $n \equiv 15 \pmod{16}$
-- statement:
--   Let $C$ denote the Collatz step map. The assertion is that every $n \equiv 15 \pmod{16}$ has a finite stopping time:
--
--   $$\exists m \in \mathbb{N} : \quad C^{m}(n) < n .$$
--
--   This class is **open**, and it is the most resistant of the classes left by the residue refinement. Writing $n = 16j + 15$, the first eight steps are parity-determined and carry $n$ to $81j + 80$: four ascending steps against four halvings give an accumulated multiplier of $3^{4}/2^{4} = 81/16 > 1$, so the orbit is far above its starting point when the residue stops determining the parity. This is the class of longest initial ascending runs at this modulus, and refining the modulus splits it further without terminating.
--
--   The statement covers the two classes $15$ and $31$ modulo $32$, and is one of the open cases left by the modulo $32$ refinement of the descent problem, alongside $7 \bmod 32$ and $27 \bmod 32$. Together they carry the whole remaining difficulty of the descent principle, and hence of the Collatz conjecture.
--
--   **Formalization Note.** No positivity hypothesis is needed: $n \equiv 15 \pmod{16}$ forces $n \ge 15$. The index $m$ is unconstrained, but $m = 0$ can never witness the conclusion since $n < n$ is false.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, https://websites.umich.edu/~lagarias/3x%2B1.html, Section 2 (stopping time is determined by n mod 2^k; the Terras-Everett analysis of coefficient stopping time). Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Mathlib
import Definitions.Def_collatzStepMap

theorem collatz_descent_fifteen_mod_sixteen (n : ℕ) (h : n % 16 = 15) :
    ∃ m : ℕ, collatzStep^[m] n < n := by
  sorry

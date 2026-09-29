-- Prove2me | Theorems.Thm_collatz_descent_three_mod_four
-- name    : collatz_descent_three_mod_four
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-08T03:52:33.042232+00:00
-- url     : https://prove2.me/theorems/8c65aab0-668b-4a40-ac63-6534f937da32
-- title:
--   Collatz descent for $n \equiv 3 \pmod 4$
-- statement:
--   Let $C$ denote the Collatz step map. The assertion is that every starting value congruent to $3$ modulo $4$ has a finite stopping time: for each $n$ with $n \equiv 3 \pmod 4$ there is an $m \in \mathbb{N}$ with
--
--   $$C^{m}(n) < n .$$
--
--   This is the one residue class modulo $4$ that elementary parity bookkeeping does not settle. For even $n$ a single step suffices, and for $n \equiv 1 \pmod 4$ with $n > 1$ three steps suffice, because $n = 4k+1$ is carried to $3k+1$. For $n \equiv 3 \pmod 4$ the first two steps produce $(3n+1)/2 > n$, and no bounded number of steps works uniformly: the length of the initial ascending run is governed by the $2$-adic behaviour of $n$ and is unbounded over the class.
--
--   The statement is open. It is the substantive content of the general descent principle for the Collatz map, and by the residue-class decomposition it is equivalent to that principle; the descent principle in turn implies the Collatz conjecture by strong induction. Tao's theorem gives descent for almost all $n$ in the sense of logarithmic density, which does not cover any specified starting value, and finite verification up to $2^{68}$ does not constrain larger $n$.
--
--   **Formalization Note.** No positivity hypothesis is needed: $n \equiv 3 \pmod 4$ already forces $n \ge 3$. The index $m$ is unconstrained, but $m = 0$ can never witness the conclusion since $n < n$ is false, so the statement genuinely asserts descent after a positive number of steps.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, https://websites.umich.edu/~lagarias/3x%2B1.html, Section 2 (stopping time and the residue classes mod 4); Terence Tao, Almost All Orbits of the Collatz Map Attain Almost Bounded Values, Forum of Mathematics Pi 10 (2022), https://arxiv.org/abs/1909.03562

import Mathlib
import Definitions.Def_collatzStepMap

theorem collatz_descent_three_mod_four (n : ℕ) (h : n % 4 = 3) :
    ∃ m : ℕ, collatzStep^[m] n < n := by
  sorry

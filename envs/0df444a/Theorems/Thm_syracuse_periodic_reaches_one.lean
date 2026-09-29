-- Prove2me | Theorems.Thm_syracuse_periodic_reaches_one
-- name    : syracuse_periodic_reaches_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T20:42:28.842405+00:00
-- url     : https://prove2.me/theorems/a46524f0-afd4-4232-b74a-8a95d7ab31a5
-- title:
--   A Syracuse-periodic point that reaches $1$ equals $1$
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map. A periodic point of $T$ whose orbit ever reaches $1$ must itself be $1$:
--   $$T^{a}(z)=z,\ a\ge 1,\ \exists k\ T^{k}(z)=1 \quad\Longrightarrow\quad z=1 .$$
--
--   **Mathematical role.** Cycles and convergence to $1$ are mutually exclusive, and this states it in the form actually needed. Every exclusion of a specific accelerated cycle length ends the same way: the argument bounds the cycle below by some explicit threshold $B$, and one is left checking that no small value is periodic. That final check is a statement about each individual residual value and has to be redone for each period.
--
--   This lemma removes that repetition. Because $1$ is fixed by $T$, an orbit which reaches $1$ stays there; a periodic orbit, on the other hand, returns to its starting point at every multiple of its length. Running far enough forward that both apply forces the starting point to equal $1$. The conclusion holds for every period $a$ at once, so it replaces the residual step uniformly: once one knows that the odd numbers below a threshold all reach $1$ under $T$, no nontrivial cycle can have its minimum among them, whatever its length.
--
--   Combined with the bound $m \lesssim a\,3^{a-1}$ on the minimum of an accelerated cycle, this reduces the entire cycle problem to convergence for small values: a nontrivial $T$-cycle of length $a$ would have to have its minimum among the odd numbers up to roughly $a\,3^{a-1}$, none of which may reach $1$.
--
--   **Formalization note.** The hypothesis is $T^{a}(z)=z$ for some positive $a$, not that $a$ is minimal. No positivity or oddness assumption on $z$ is needed; reaching $1$ supplies both.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem CollatzMission.collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 8 (cycles), https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_periodic_reaches_one (z a : ℕ) (ha : 0 < a)
    (hcyc : syracuseStep^[a] z = z) (hreach : ∃ k : ℕ, syracuseStep^[k] z = 1) :
    z = 1 := by sorry

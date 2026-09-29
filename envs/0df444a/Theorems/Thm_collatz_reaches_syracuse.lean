-- Prove2me | Theorems.Thm_collatz_reaches_syracuse
-- name    : collatz_reaches_syracuse
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:27:21.621637+00:00
-- url     : https://prove2.me/theorems/50fdd64a-df1d-498d-916b-5fcf9845d357
-- title:
--   One Syracuse step is finitely many Collatz steps
-- statement:
--   Let $C$ be the Collatz step map and $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ the Syracuse map. For every odd $n$ there is a positive number of Collatz steps carrying $n$ exactly to $T(n)$:
--
--   $$n \text{ odd} \quad \Longrightarrow \quad \exists M > 0 : \ C^{M}(n) = T(n) .$$
--
--   The witness is $M = v_2(3n+1) + 1$. Since $n$ is odd the first Collatz step is the ascending one, $C(n) = 3n+1$; writing $3n+1 = 2^{v} \cdot T(n)$ with $v = v_2(3n+1)$, the next $v$ steps are halvings and divide out $2^{v}$ exactly.
--
--   This is the precise sense in which the Syracuse map accelerates the Collatz map: it is not an approximation or a model, but a subsequence of the same orbit. Consequently any statement about $T$-orbits transfers verbatim to a statement about $C$-orbits.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 2 (the function T and its relation to the Collatz map), https://websites.umich.edu/~lagarias/3x%2B1.html; Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Mathlib
import Definitions.Def_collatzStepMap
import Definitions.Def_syracuseStep

theorem collatz_reaches_syracuse (n : ℕ) (hn : ¬ Even n) :
    ∃ M : ℕ, 0 < M ∧ collatzStep^[M] n = syracuseStep n := by
  sorry

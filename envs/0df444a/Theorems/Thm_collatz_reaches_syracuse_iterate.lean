-- Prove2me | Theorems.Thm_collatz_reaches_syracuse_iterate
-- name    : collatz_reaches_syracuse_iterate
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:27:24.87271+00:00
-- url     : https://prove2.me/theorems/9ee87804-6ee2-4f12-8594-d5f791166dc2
-- title:
--   Syracuse orbits are subsequences of Collatz orbits
-- statement:
--   Let $C$ be the Collatz step map and $T$ the Syracuse map. For odd $n$, every point of the $T$-orbit of $n$ occurs on the $C$-orbit of $n$:
--
--   $$n \text{ odd} \quad \Longrightarrow \quad \forall t \ \exists M : \ C^{M}(n) = T^{t}(n) .$$
--
--   The proof is induction on $t$, using at each stage that $T^{t}(n)$ is again odd, so that a single $T$-step from it is realised by finitely many $C$-steps, and that the two orbit segments compose through $C^{M'+M}(n) = C^{M'}(C^{M}(n))$.
--
--   The statement identifies the $T$-orbit as the subsequence of odd values along the $C$-orbit. It is the transfer principle that lets the quantitative theory of the accelerated map — where the expected multiplier per step is $3/4$ — be applied to the original problem without loss.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 2 (the function T and its relation to the Collatz map), https://websites.umich.edu/~lagarias/3x%2B1.html; Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Mathlib
import Definitions.Def_collatzStepMap
import Definitions.Def_syracuseStep

theorem collatz_reaches_syracuse_iterate (n : ℕ) (hn : ¬ Even n) (t : ℕ) :
    ∃ M : ℕ, collatzStep^[M] n = syracuseStep^[t] n := by
  sorry

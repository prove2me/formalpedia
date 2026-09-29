-- Prove2me | Theorems.Thm_syracuse_cycle_pow_two_gt_pow_three
-- name    : syracuse_cycle_pow_two_gt_pow_three
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T18:57:21.98272+00:00
-- url     : https://prove2.me/theorems/955877f3-88bd-4837-b1d9-2e4467430637
-- title:
--   Any Syracuse cycle satisfies $2^{K} > 3^{a}$
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. Suppose $m>0$ lies on a $T$-cycle of length $a \ge 1$, so that $T^{a}(m) = m$, and write
--   $$x_i = T^{i}(m), \qquad v_i = v_2(3x_i+1), \qquad K = \sum_{i=0}^{a-1} v_i$$
--   for the orbit and the total number of halvings consumed in one period. Then
--   $$3^{a} \;<\; 2^{K}.$$
--
--   In words: around any Collatz cycle, the halvings strictly outweigh the triplings. Equivalently $K/a > \log_2 3$, so the ratio of even steps to odd steps in a cycle is a rational number lying strictly above $\log_2 3 = 1.5849625\ldots$
--
--   **Mathematical role.** This is the elementary half of the classical approach to cycle exclusion. Pairing it with the complementary upper bound — which comes from the fact that every orbit element is at least the cycle's minimum — traps $K/a$ in a narrow window around $\log_2 3$, forcing $K/a$ to be an unusually good rational approximation to an irrational number. Bounds on how well $\log_2 3$ can be approximated by rationals, supplied by continued fractions and in sharper form by Baker-type estimates for linear forms in logarithms, then force the period $a$ to be enormous. That is the route by which nontrivial Collatz cycles are constrained without any appeal to the descent principle.
--
--   Stated on its own, this inequality does **not** exclude any cycle: the trivial cycle $1 \mapsto 1$ satisfies it, with $a=1$, $K=2$ and $3 < 4$. It is a necessary condition, and it is the entry point that the transcendence argument needs.
--
--   **Formalization note.** No oddness hypothesis is required. The valuation is written as `Nat.factorization` at the prime $2$, and the total $K$ as a sum over `Finset.range a`. Only $m>0$, $a>0$ and $T^{a}(m)=m$ are assumed; in particular $m$ need not be the minimum of its cycle.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem CollatzMission.collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 8 (cycles and the inequality 2^K > 3^a), https://websites.umich.edu/~lagarias/3x%2B1.html; Ray P. Steiner, A theorem on the syracuse problem, Proc. 7th Manitoba Conf. on Numerical Mathematics (1977), 553-559

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_cycle_pow_two_gt_pow_three (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hcyc : syracuseStep^[a] m = m) :
    3 ^ a < 2 ^ (∑ i ∈ Finset.range a, (3 * syracuseStep^[i] m + 1).factorization 2) := by sorry

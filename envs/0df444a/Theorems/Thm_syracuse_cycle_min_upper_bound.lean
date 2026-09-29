-- Prove2me | Theorems.Thm_syracuse_cycle_min_upper_bound
-- name    : syracuse_cycle_min_upper_bound
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T19:05:27.086046+00:00
-- url     : https://prove2.me/theorems/514577b7-9148-4a35-a0b2-80ac16b8b322
-- title:
--   Cycle minimum bounds the halving count: $2^{K}m^{a} \le (3m+1)^{a}$
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map. Suppose $m>0$ lies on a $T$-cycle of length $a\ge 1$ and is a **minimum** of that cycle, so $T^{a}(m)=m$ and $m \le T^{i}(m)$ for every $i$. Writing $K = \sum_{i<a} v_2(3x_i+1)$ for the total number of halvings in one period, with $x_i = T^{i}(m)$,
--   $$2^{K}\, m^{a} \;\le\; (3m+1)^{a}.$$
--
--   Equivalently, dividing by $m^a$,
--   $$2^{K} \;\le\; \Big(3 + \tfrac{1}{m}\Big)^{a}, \qquad\text{that is}\qquad \frac{K}{a} \;\le\; \log_2\!\Big(3+\frac1m\Big).$$
--
--   **Mathematical role.** This is the counterpart to the lower bound $3^a < 2^K$, i.e. $K/a > \log_2 3$. Together the two confine the ratio of even steps to odd steps in a cycle to the narrow window
--   $$\log_2 3 \;<\; \frac{K}{a} \;\le\; \log_2\!\Big(3+\frac1m\Big),$$
--   whose width is on the order of $1/(m \ln 2 \cdot 3)$. A rational number with denominator $a$ can only land in an interval that short when $a$ is large compared with $m$: the period of a Collatz cycle must grow in proportion to its smallest element. This is the elementary mechanism by which computational verification of the conjecture up to some height converts into a lower bound on the period of any hypothetical nontrivial cycle, and it is the point where sharper irrationality measures for $\log_2 3$ — continued fractions, and in stronger form Baker-type bounds for linear forms in logarithms — enter the classical literature.
--
--   The bound is sharp: the trivial cycle has $m=1$, $a=1$, $K=2$, and $2^2 \cdot 1 = 4 = (3\cdot 1+1)^1$, with equality.
--
--   **Formalization note.** Minimality is stated over the whole forward orbit, $\forall i,\ m \le T^{i}(m)$, which for a cycle is the same as minimality over the cycle. No oddness hypothesis is needed. The hypothesis $a>0$ is stated for uniformity with the companion lower bound but is not used: at $a=0$ both sides are $1$.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem CollatzMission.collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 8 (cycles, the window for K/a and period lower bounds), https://websites.umich.edu/~lagarias/3x%2B1.html; Ray P. Steiner, A theorem on the syracuse problem, Proc. 7th Manitoba Conf. on Numerical Mathematics (1977), 553-559

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_cycle_min_upper_bound (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hcyc : syracuseStep^[a] m = m)
    (hmin : ∀ i : ℕ, m ≤ syracuseStep^[i] m) :
    2 ^ (∑ i ∈ Finset.range a, (3 * syracuseStep^[i] m + 1).factorization 2) * m ^ a
      ≤ (3 * m + 1) ^ a := by sorry

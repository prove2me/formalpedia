-- Prove2me | Theorems.Thm_syracuse_cycle_min_bound
-- name    : syracuse_cycle_min_bound
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T20:18:27.752529+00:00
-- url     : https://prove2.me/theorems/155de86d-ddde-4c52-90d0-ec4973bef059
-- title:
--   Cycle minimum is at most $\approx a\,3^{a-1}$
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map. If $m$ is the smallest element of a $T$-cycle of length $a \ge 1$, then
--   $$\big(3^{a}+1\big)\,m^{a} \;\le\; (3m+1)^{a}.$$
--
--   **What it says.** Dividing by $m^{a}$, the inequality reads $3^{a}+1 \le (3+1/m)^{a}$. The right-hand side exceeds $3^{a}$ by roughly $a\,3^{a-1}/m$, so the inequality can hold only when
--   $$m \;\lesssim\; a\,3^{\,a-1} .$$
--   The bound is essentially exact: the largest $m$ satisfying it is $1, 6, 27, 108, 405, 1458, 5103$ for $a = 1,\dots,7$, against $a\,3^{a-1} = 1, 6, 27, 108, 405, 1458, 5103$.
--
--   **Mathematical role.** This is a single statement constraining *every* cycle length at once, in contrast to the case-by-case exclusions of individual short periods. It says the minimum of a Collatz cycle cannot be large relative to its accelerated length — equivalently, that a cycle whose elements are all big must be very long. Paired with computational verification of the conjecture up to some height $H$, which forces $m > H$ for any nontrivial cycle, it converts directly into a lower bound on the period: any nontrivial cycle must satisfy $a\,3^{a-1} \gtrsim H$. This is the standard route by which numerical verification yields period bounds, and it is the reason no short cycle can hide among large integers.
--
--   The proof is a two-line consequence of two facts about cycles: that the halvings strictly outweigh the triplings, $3^{a} < 2^{K}$, and that the minimum bounds the halving count, $2^{K}m^{a} \le (3m+1)^{a}$. The first gives $2^{K} \ge 3^{a}+1$ purely because $2^{K}$ is an integer, and substituting that into the second yields the claim. No Diophantine input is used, and the descent principle is not assumed.
--
--   **Formalization note.** Minimality is stated over the whole forward orbit, $\forall i,\ m \le T^{i}(m)$, which for a cycle is minimality over the cycle. No oddness hypothesis is needed. The exponent $K$ has been eliminated from the statement, leaving a closed inequality in $m$ and $a$ alone.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem CollatzMission.collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 8 (cycles and period lower bounds from numerical verification), https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_cycle_min_bound (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hcyc : syracuseStep^[a] m = m)
    (hmin : ∀ i : ℕ, m ≤ syracuseStep^[i] m) :
    (3 ^ a + 1) * m ^ a ≤ (3 * m + 1) ^ a := by sorry

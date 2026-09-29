-- Prove2me | Theorems.Thm_syracuse_fixed_point_eq_one
-- name    : syracuse_fixed_point_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T19:13:12.991492+00:00
-- url     : https://prove2.me/theorems/d23b36da-e6a1-45cb-b48a-a970df008e7b
-- title:
--   The only positive fixed point of the Syracuse map is $1$
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. Its only positive fixed point is $1$:
--   $$T(m) = m,\ m>0 \quad\Longrightarrow\quad m = 1.$$
--
--   **Mathematical role.** In the accelerated dynamics a Collatz cycle of length $a$ is exactly a point with $T^{a}(m)=m$, so this is the case $a=1$ of cycle exclusion, settled unconditionally. Writing $2^{v}$ for the power of two dividing $3m+1$, the fixed-point equation says $2^{v}m = 3m+1$, that is
--   $$m\,(2^{v}-3) = 1 ,$$
--   which in the natural numbers forces $m=1$ and $2^{v}=4$ — the familiar $1 \mapsto 4 \mapsto 2 \mapsto 1$ loop of the classical map, collapsed to a single accelerated step.
--
--   This is the one case of the cycle problem that needs no information about how well $\log_2 3$ can be approximated by rationals. For $a \ge 2$ the analogous elimination requires the window $\log_2 3 < K/a \le \log_2(3+1/m)$ to contain no admissible integer $K$, which is a genuine Diophantine question; for $a=1$ the window argument degenerates and bare divisibility suffices.
--
--   **Formalization note.** No oddness hypothesis is needed: a fixed point of $T$ is automatically odd, since $T$ always returns an odd part. The valuation is written as `Nat.factorization` at the prime $2$.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem CollatzMission.collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 8 (cycles), https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_fixed_point_eq_one (m : ℕ) (hm : 0 < m) (hfix : syracuseStep m = m) :
    m = 1 := by sorry

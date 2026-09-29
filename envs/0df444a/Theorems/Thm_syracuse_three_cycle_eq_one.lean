-- Prove2me | Theorems.Thm_syracuse_three_cycle_eq_one
-- name    : syracuse_three_cycle_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T19:37:08.945872+00:00
-- url     : https://prove2.me/theorems/ba8ad12a-a871-4c7e-af16-bcd521ebbb96
-- title:
--   No nontrivial Syracuse cycle of length $3$
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map. Its only positive point of period dividing $3$ is $1$:
--   $$T^{3}(m) = m,\ m>0 \quad\Longrightarrow\quad m = 1 .$$
--
--   Equivalently, the Collatz map has no nontrivial cycle whose accelerated form has length $3$.
--
--   **Mathematical role.** Together with the corresponding statements for periods $1$ and $2$, this closes the three shortest cases of the cycle problem unconditionally. Writing $x_0=m$, $x_1=T(m)$, $x_2=T^2(m)$ and multiplying the three step relations $2^{v_i}x_{i+1}=3x_i+1$ gives
--   $$\big(2^{K}-27\big)\,x_0x_1x_2 \;=\; 9\,(x_0x_1+x_0x_2+x_1x_2) \;+\; 3\,(x_0+x_1+x_2) \;+\; 1 ,$$
--   where $K=v_0+v_1+v_2$. The right-hand side is positive, so $2^{K}>27$, and a power of two exceeding $27$ is at least $32$; hence the left-hand side is at least $5\,x_0x_1x_2$. That inequality cannot hold when all three orbit points are $\ge 7$, since then the cubic term dominates the quadratic and linear ones. So the cycle meets $\{1,3,5\}$, and of those only $1$ is periodic: $3 \mapsto 5 \mapsto 1$ and $5 \mapsto 1$ both fall into the trivial cycle.
--
--   The interest is again that no Diophantine input appears. For a cycle of length $a$ the general bounds confine the ratio of even to odd steps to $\log_2 3 < K/a \le \log_2(3+1/m)$, and eliminating a given $a$ means showing this window holds no admissible integer $K$ — a question about rational approximations to $\log_2 3$. For small $a$ the gap between $2^{K}$ and $3^{a}$ is necessarily coarse ($32$ against $27$ here), leaving enough slack for plain integrality. That slack shrinks quickly as $a$ grows — at $a=5$ the gap is only $256-243=13$ — so this elementary ladder reaches a few more cases at most and does not extend to all periods.
--
--   **Formalization note.** No oddness hypothesis is needed: a point of period dividing $3$ under $T$ is automatically odd, since $T$ returns an odd part. The statement covers periods $1$ and $3$ simultaneously, as period $1$ divides $3$.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem CollatzMission.collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 8 (cycles), https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_three_cycle_eq_one (m : ℕ) (hm : 0 < m) (hcyc : syracuseStep^[3] m = m) :
    m = 1 := by sorry

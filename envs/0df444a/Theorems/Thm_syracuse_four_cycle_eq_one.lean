-- Prove2me | Theorems.Thm_syracuse_four_cycle_eq_one
-- name    : syracuse_four_cycle_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T19:51:00.71029+00:00
-- url     : https://prove2.me/theorems/3436eeb1-826e-4cab-a160-94ffb3c11732
-- title:
--   No nontrivial Syracuse cycle of length $4$
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map. Its only positive point of period dividing $4$ is $1$:
--   $$T^{4}(m) = m,\ m>0 \quad\Longrightarrow\quad m = 1 .$$
--
--   Equivalently, the Collatz map has no nontrivial cycle whose accelerated form has length $4$.
--
--   **Mathematical role.** With the corresponding statements for periods $1$, $2$ and $3$, this closes every accelerated cycle length up to $4$ unconditionally. Writing $x_0=m,\dots,x_3$ for the orbit and multiplying the four step relations $2^{v_i}x_{i+1}=3x_i+1$ gives
--   $$\big(2^{K}-81\big)\,P \;=\; 27 e_3 + 9 e_2 + 3 e_1 + 1 ,$$
--   where $P=x_0x_1x_2x_3$, $K=\sum v_i$, and $e_j$ is the $j$-th elementary symmetric function of the orbit. The right-hand side is positive, so $2^{K}>81$, and the next power of two is $128$ — leaving the generous margin $2^{K}-81 \ge 47$. That margin is incompatible with all four orbit points being at least $3$, so the cycle meets $\{1\}$, and $1$ is fixed.
--
--   **Why this is where the elementary method stops.** The slack driving these proofs is the gap between $2^{K}$ and $3^{a}$. It is wide at $a=4$ — $128$ against $81$, a ratio of $1.58$ — which is why this case is in fact easier than $a=3$. At $a=5$ it collapses: $2^{8}=256$ against $3^{5}=243$, a ratio of $1.05$. That is not an accident. The admissible ratio satisfies $K/a > \log_2 3 = 1.5849\ldots$, and $8/5 = 1.6$ is a continued-fraction convergent of $\log_2 3$, so the power of two can crowd $3^{a}$ arbitrarily closely along the convergents. Excluding those periods is exactly a question about how well $\log_2 3$ is approximated by rationals, and no amount of elementary product manipulation replaces it.
--
--   **Formalization note.** No oddness hypothesis is needed: a point of period dividing $4$ under $T$ is automatically odd. The statement covers periods $1$, $2$ and $4$ simultaneously, since each divides $4$.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem CollatzMission.collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 8 (cycles), https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_four_cycle_eq_one (m : ℕ) (hm : 0 < m) (hcyc : syracuseStep^[4] m = m) :
    m = 1 := by sorry

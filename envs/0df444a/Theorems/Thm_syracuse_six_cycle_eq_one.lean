-- Prove2me | Theorems.Thm_syracuse_six_cycle_eq_one
-- name    : syracuse_six_cycle_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T21:02:05.67001+00:00
-- url     : https://prove2.me/theorems/07276f58-8c22-4ef9-909a-1de723575397
-- title:
--   No nontrivial Syracuse cycle of length $6$
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map. Its only positive point of period dividing $6$ is $1$:
--   $$T^{6}(m) = m,\ m>0 \quad\Longrightarrow\quad m = 1 .$$
--
--   Equivalently, the Collatz map has no nontrivial cycle whose accelerated form has length $6$.
--
--   **Mathematical role.** With the shorter lengths this closes every accelerated cycle length up to $6$. Multiplying the six step relations $2^{v_i}x_{i+1}=3x_i+1$ around the orbit gives
--   $$\big(2^{K}-729\big)\,P \;=\; 243 e_5 + 81 e_4 + 27 e_3 + 9 e_2 + 3 e_1 + 1 ,$$
--   with $P$ the product of the orbit and $e_j$ its elementary symmetric functions. Positivity of the right side forces $2^{K}>729$, hence $2^{K}\ge 1024$ and a margin of $295$ — a generous one, so the comparison already fails once every orbit point is at least $7$.
--
--   This case is notably easier than length $5$, where the margin was only $13$ and the threshold rose to $33$. The margin is governed by how far the least power of two above $3^{a}$ has to reach, and at $a=6$ it reaches from $729$ to $1024$.
--
--   **On the residual step.** Earlier exclusions each finished with a hand check that no small value is periodic of that particular length. That is no longer needed: it is now known that no nontrivial $T$-cycle contains an element at most $33$, whatever its length, so the threshold $7$ obtained here is immediately enough. The exclusion therefore consists of the symmetric-function comparison alone.
--
--   **Formalization note.** No oddness hypothesis is needed: a point of period dividing $6$ under $T$ is automatically odd. The statement covers lengths $1$, $2$, $3$ and $6$ simultaneously, since each divides $6$.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem CollatzMission.collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 8 (cycles), https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_six_cycle_eq_one (m : ℕ) (hm : 0 < m) (hcyc : syracuseStep^[6] m = m) :
    m = 1 := by sorry

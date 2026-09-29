-- Prove2me | Theorems.Thm_syracuse_five_cycle_eq_one
-- name    : syracuse_five_cycle_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T20:11:22.887884+00:00
-- url     : https://prove2.me/theorems/7b544e6c-8826-4316-ab06-5022b837ccd0
-- title:
--   No nontrivial Syracuse cycle of length $5$
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map. Its only positive point of period dividing $5$ is $1$:
--   $$T^{5}(m) = m,\ m>0 \quad\Longrightarrow\quad m = 1 .$$
--
--   Equivalently, the Collatz map has no nontrivial cycle whose accelerated form has length $5$.
--
--   **Mathematical role.** With the cases $a \le 4$ this closes every accelerated cycle length up to $5$ unconditionally. Multiplying the five step relations $2^{v_i}x_{i+1}=3x_i+1$ around the orbit and writing $P=\prod x_i$, $K=\sum v_i$ gives
--   $$\big(2^{K}-243\big)\,P \;=\; 81 e_4 + 27 e_3 + 9 e_2 + 3 e_1 + 1 ,$$
--   with $e_j$ the elementary symmetric functions of the orbit. Positivity of the right side forces $2^{K}>243$, hence $2^{K}\ge 256$ and a margin of $13$.
--
--   This case is markedly tighter than its predecessors. The margin $2^{K}-3^{a}$ is $47$ at $a=4$ but only $13$ here, because $8/5=1.6$ is a continued-fraction convergent of $\log_2 3 = 1.5849\ldots$, so $2^{8}=256$ sits unusually close above $3^{5}=243$. The consequence is not that the elementary method fails, but that it needs a larger threshold: the comparison $81e_4 + 27e_3 + 9e_2 + 3e_1 + 1 < 13P$ holds once every orbit point is at least $33$, whereas $3$ sufficed at $a=4$. The residual check is correspondingly larger — the sixteen odd values below $33$ — and none of them is $5$-periodic.
--
--   **On how far this goes.** Each individual period is decidable this way: for a given $a$, the margin determines a finite threshold $B_a$, and one checks the odd values below it. What does not follow is the general statement, which needs all $a$ at once, and the thresholds grow with the quality of the rational approximations to $\log_2 3$. Excluding all periods uniformly remains a question about linear forms in logarithms.
--
--   **Formalization note.** No oddness hypothesis is needed: a point of period dividing $5$ under $T$ is automatically odd. The statement covers period $1$ as well, since $1$ divides $5$.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem CollatzMission.collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 8 (cycles), https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_five_cycle_eq_one (m : ℕ) (hm : 0 < m) (hcyc : syracuseStep^[5] m = m) :
    m = 1 := by sorry

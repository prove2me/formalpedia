-- Prove2me | Theorems.Thm_syracuse_period_le_fortyninesixty_eq_one
-- name    : syracuse_period_le_fortyninesixty_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:21:50.846294+00:00
-- url     : https://prove2.me/theorems/1f75404a-e93a-4c58-8dca-d6a968bed177
-- title:
--   No nontrivial Syracuse cycle of period at most 4960
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $m$ is a positive integer with $T^a(m) = m$ for some $a$ with $1 \le a \le 4960$, then $m = 1$.
--
--   Equivalently, every Syracuse cycle of length at most $4960$ is the trivial cycle $\{1\}$; the return time need not be minimal.
--
--   Periods up to $4295$ are already settled, so only $4296 \le a \le 4960$ need fresh work: for each such $a$ one checks the single numerical inequality
--   $$5650297^a \ <\ 2^{K_a}\cdot 1883432^a ,$$
--   where $K_a$ is the least exponent with $3^a < 2^{K_a}$, and feeds it to the margin criterion. The threshold $1883432$ is available because no nontrivial cycle contains a value below it.
--
--   Period $4961$ is the first not covered. Writing $B(a)$ for the least threshold covering every period up to $a$, the sequence reads $34, 147, 387, 1193, 3343, 6725, 12825, 27114, 99781, 330750, 583288, 860564, 1166400, 1505449, 1883432$ as $a$ passes $16, 28, 40, 93, 146, 199, 252, 305, 970, 1635, 2300, 2965, 3630, 4295, 4960$, the jumps landing on denominators of convergents of $\log_2 3$. Since $B(a) \to \infty$, no single threshold covers every period, so a finite verification of this kind can never settle the cycle question; equally, no finite period defeats the method — only the certificate size grows without bound.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_cycle_eq_one_of_margin_at (756c30cf-ce03-4b10-afe8-8f76f671ae4f), syracuse_no_cycle_below_1883432, and syracuse_period_le_fortytwoninetyfive_eq_one for the periods already settled.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_period_le_fortyninesixty_eq_one (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hle : a ≤ 4960) (hcyc : syracuseStep^[a] m = m) : m = 1 := by sorry

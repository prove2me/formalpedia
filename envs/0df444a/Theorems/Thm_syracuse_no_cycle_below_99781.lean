-- Prove2me | Theorems.Thm_syracuse_no_cycle_below_99781
-- name    : syracuse_no_cycle_below_99781
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T05:32:11.835835+00:00
-- url     : https://prove2.me/theorems/bb9842e2-a1a4-46c0-be27-ea9e7d8a90a5
-- title:
--   No nontrivial Syracuse cycle contains a value below 99781
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $z$ is a positive integer with $z \le 99780$ and $T^a(z) = z$ for some $a \ge 1$, then $z = 1$.
--
--   The return time $a$ is arbitrary — no minimality is assumed — so the statement says that the only Syracuse cycle meeting the interval $[1, 99780]$ is the trivial cycle $\{1\}$.
--
--   It follows from the finite verification that every odd number below $99781$ reaches $1$, together with the observation that a periodic point of $T$ whose orbit reaches $1$ must itself be $1$, since $T(1) = 1$ is absorbing. This raises the small-value threshold from the previously established bound of $27113$, and is the input that lets the margin criterion exclude every cycle of period at most $970$.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; extension of syracuse_no_cycle_below_27114 (f56b97a4-527b-4005-8f1a-4f6e2f3250eb), via syracuse_reaches_one_below_99781 and syracuse_periodic_reaches_one (a46524f0-afd4-4232-b74a-8a95d7ab31a5).

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_no_cycle_below_99781 (z a : ℕ) (hz : 0 < z) (ha : 0 < a) (hle : z ≤ 99780)
    (hcyc : syracuseStep^[a] z = z) : z = 1 := by sorry

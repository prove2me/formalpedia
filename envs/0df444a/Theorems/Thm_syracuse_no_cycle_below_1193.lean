-- Prove2me | Theorems.Thm_syracuse_no_cycle_below_1193
-- name    : syracuse_no_cycle_below_1193
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T03:40:29.255952+00:00
-- url     : https://prove2.me/theorems/0a8acd74-1c2f-44f3-94ab-e3151ddcda9e
-- title:
--   No nontrivial Syracuse cycle contains a value below 1193
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $z$ is a positive integer with $z \le 1192$ and $T^a(z) = z$ for some $a \ge 1$, then $z = 1$.
--
--   The return time $a$ is arbitrary — no minimality is assumed — so the statement says that the only Syracuse cycle meeting the interval $[1, 1192]$ is the trivial cycle $\{1\}$.
--
--   It follows from the finite verification that every odd number below $1193$ reaches $1$, together with the observation that a periodic point of $T$ whose orbit reaches $1$ must itself be $1$ (since $T(1)=1$ is absorbing). This raises the small-value threshold from the previously established bound of $33$, and is the input that lets the margin criterion exclude every cycle of period at most $93$.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; extension of syracuse_no_small_cycle (f2ae2367-c0d1-487d-b130-29f6669676db) from bound 33 to bound 1192, via syracuse_reaches_one_below_1193 and syracuse_periodic_reaches_one (a46524f0-afd4-4232-b74a-8a95d7ab31a5).

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_no_cycle_below_1193 (z a : ℕ) (hz : 0 < z) (ha : 0 < a) (hle : z ≤ 1192)
    (hcyc : syracuseStep^[a] z = z) : z = 1 := by sorry

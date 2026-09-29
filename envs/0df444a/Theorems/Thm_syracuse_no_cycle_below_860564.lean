-- Prove2me | Theorems.Thm_syracuse_no_cycle_below_860564
-- name    : syracuse_no_cycle_below_860564
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:42:14.431462+00:00
-- url     : https://prove2.me/theorems/0356bf9d-c641-4ace-b979-a3b83d286afb
-- title:
--   No nontrivial Syracuse cycle contains a value below 860564
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $z$ is a positive integer with $z \le 860563$ and $T^a(z) = z$ for some $a \ge 1$, then $z = 1$. The return time is arbitrary; no minimality is assumed.
--
--   Pass to the least value $w$ on the orbit of $z$. Then $w \le z < 860564$, and $w$ is odd and positive because it is a value of $T$. Were $w$ greater than $1$ it would admit a strictly smaller iterate by the descent result for this range — impossible, since $w$ is the orbit minimum. Hence $w = 1$, the orbit of $z$ reaches $1$, and a periodic point whose orbit reaches $1$ is itself $1$.
--
--   Only descent is used, never convergence; that is what keeps the threshold cheap to raise.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_descends_below_860564 and syracuse_periodic_reaches_one (a46524f0-afd4-4232-b74a-8a95d7ab31a5).

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_no_cycle_below_860564 (z a : ℕ) (hz : 0 < z) (ha : 0 < a) (hle : z ≤ 860563)
    (hcyc : syracuseStep^[a] z = z) : z = 1 := by sorry

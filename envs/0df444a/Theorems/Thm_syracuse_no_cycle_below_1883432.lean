-- Prove2me | Theorems.Thm_syracuse_no_cycle_below_1883432
-- name    : syracuse_no_cycle_below_1883432
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:21:52.367596+00:00
-- url     : https://prove2.me/theorems/33c2cf17-1597-4cb1-b85c-28dd910af0c9
-- title:
--   No nontrivial Syracuse cycle contains a value below 1883432
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $z$ is a positive integer with $z \le 1883431$ and $T^a(z) = z$ for some $a \ge 1$, then $z = 1$. The return time is arbitrary; no minimality is assumed.
--
--   Pass to the least value $w$ on the orbit of $z$. Then $w \le z < 1883432$, and $w$ is odd and positive because it is a value of $T$. Were $w$ greater than $1$ it would admit a strictly smaller iterate by the descent result for this range — impossible, since $w$ is the orbit minimum. Hence $w = 1$, the orbit of $z$ reaches $1$, and a periodic point whose orbit reaches $1$ is itself $1$.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_descends_below_1883432 and syracuse_periodic_reaches_one (a46524f0-afd4-4232-b74a-8a95d7ab31a5).

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_no_cycle_below_1883432 (z a : ℕ) (hz : 0 < z) (ha : 0 < a) (hle : z ≤ 1883431)
    (hcyc : syracuseStep^[a] z = z) : z = 1 := by sorry

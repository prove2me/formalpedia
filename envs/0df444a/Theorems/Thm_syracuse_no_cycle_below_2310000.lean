-- Prove2me | Theorems.Thm_syracuse_no_cycle_below_2310000
-- name    : syracuse_no_cycle_below_2310000
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-23T19:05:28.602929+00:00
-- url     : https://prove2.me/theorems/73735589-bbad-479f-8d7e-375fd2f82875
-- title:
--   No nontrivial Syracuse cycle below 2310000
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $z$ is a positive integer with $z \le 2309999$ and $T^a(z) = z$ for some $a \ge 1$, then $z = 1$. The return time is arbitrary; no minimality is assumed.
--
--   Pass to the least value $w$ on the orbit of $z$. Then $w \le z < 2310000$, and $w$ is odd and positive because it is a value of $T$. Were $w$ greater than $1$ it would admit a strictly smaller iterate by the descent result for this range — impossible, since $w$ is the orbit minimum. Hence $w = 1$, the orbit of $z$ reaches $1$, and a periodic point whose orbit reaches $1$ is itself $1$.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_descends_below_2310000 and syracuse_periodic_reaches_one (a46524f0-afd4-4232-b74a-8a95d7ab31a5).

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_no_cycle_below_2310000 (z a : ℕ) (hz : 0 < z) (ha : 0 < a) (hle : z ≤ 2309999)
    (hcyc : syracuseStep^[a] z = z) : z = 1 := by sorry

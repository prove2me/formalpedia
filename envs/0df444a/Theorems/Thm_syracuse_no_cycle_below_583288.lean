-- Prove2me | Theorems.Thm_syracuse_no_cycle_below_583288
-- name    : syracuse_no_cycle_below_583288
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T18:28:48.394839+00:00
-- url     : https://prove2.me/theorems/c327f26f-7c8e-4ddd-bbd9-2f8c6d0316fa
-- title:
--   No nontrivial Syracuse cycle contains a value below 583288
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $z$ is a positive integer with $z \le 583287$ and $T^a(z) = z$ for some $a \ge 1$, then $z = 1$. The return time is arbitrary; no minimality is assumed.
--
--   Pass to the least value $w$ on the orbit of $z$. Then $w \le z < 583288$, and $w$ is odd and positive because it is a value of $T$. Were $w$ greater than $1$ it would admit a strictly smaller iterate, by the descent result for this range — impossible, since $w$ is the orbit minimum. Hence $w = 1$, the orbit of $z$ reaches $1$, and a periodic point whose orbit reaches $1$ is itself $1$.
--
--   Only descent is used, never convergence; that is what keeps the threshold cheap to raise.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_descends_below_583288 and syracuse_periodic_reaches_one (a46524f0-afd4-4232-b74a-8a95d7ab31a5). Supersedes syracuse_no_cycle_below_330750 (96774dff-bb66-4012-ba8c-ad6a91c837cb).

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_no_cycle_below_583288 (z a : ℕ) (hz : 0 < z) (ha : 0 < a) (hle : z ≤ 583287)
    (hcyc : syracuseStep^[a] z = z) : z = 1 := by sorry

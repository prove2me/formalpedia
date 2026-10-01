-- Prove2me | Theorems.Thm_syracuse_descends_below_2167436
-- name    : syracuse_descends_below_2167436
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-23T18:55:12.228651+00:00
-- url     : https://prove2.me/theorems/319f4f7d-50e8-4d00-bf87-91a952b885e1
-- title:
--   Syracuse descent below 2167436
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. Every odd $m$ with $1 < m < 2167436$ admits a $t$ with $T^t(m) < m$: below $2025436$ by the ladder stage syracuse_descends_below_2025436, and $[2025435, 2167435]$ by $71$ independent range lemmas.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; ladder stage raising the verified descent threshold to 2310000, assembled from independent range lemmas (slices 71..141).

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_below_2167436 (m : ℕ) (h1 : 1 < m) (hlt : m < 2167436) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry

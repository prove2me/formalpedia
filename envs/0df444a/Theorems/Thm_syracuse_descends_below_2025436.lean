-- Prove2me | Theorems.Thm_syracuse_descends_below_2025436
-- name    : syracuse_descends_below_2025436
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-23T18:46:37.914761+00:00
-- url     : https://prove2.me/theorems/8d56f810-b468-49b9-97bd-53025d73cb18
-- title:
--   Syracuse descent below 2025436
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. Every odd $m$ with $1 < m < 2025436$ admits a $t$ with $T^t(m) < m$: below $1883432$ by the previously verified descent bound, the single value $1883433$ by direct computation, and $[1883435, 2025435]$ by $71$ independent range lemmas.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; ladder stage raising the verified descent threshold to 2310000, assembled from independent range lemmas (slices 0..70).

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_below_2025436 (m : ℕ) (h1 : 1 < m) (hlt : m < 2025436) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry

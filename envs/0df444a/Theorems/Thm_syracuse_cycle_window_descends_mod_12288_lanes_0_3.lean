-- Prove2me | Theorems.Thm_syracuse_cycle_window_descends_mod_12288_lanes_0_3
-- name    : syracuse_cycle_window_descends_mod_12288_lanes_0_3
-- status  : Open
-- author  : @Jie Luo
-- created : 2026-11-26T11:28:30.237711+00:00
-- url     : https://prove2.me/theorems/79e30196-319f-4fb9-a730-c16a4570b3ac
-- title:
--   Syracuse descent across the shortest-period window in three residue lanes
-- statement:
--   Every odd number in [1,291,845,632, 5,710,000,000) which is 31, 47, or 71 modulo 12,288 has a strictly smaller Syracuse iterate.
-- source:
--   The first three surviving lanes of the orbit-minimum sieve after intersecting with 7 or 11 modulo 12; affine checker attributed to immiq in the source.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Card

theorem syracuse_cycle_window_descends_mod_12288_lanes_0_3 (x : ℕ) (hlo : 1291845632 ≤ x) (hhi : x < 5710000000)
    (ho : x%2=1) (hlane : x%12288 ∈ ([31,47,71] : List ℕ)) :
    ∃ t : ℕ, syracuseStep^[t] x < x := by sorry

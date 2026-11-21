-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_livePaths_prefix_bound
-- name    : Kourovka.ProductPaths.livePaths_prefix_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:43.459201+00:00
-- url     : https://prove2.me/theorems/8262ea8a-d18b-4659-9dda-fca46f04c723
-- title:
--   Product Paths: live Paths prefix bound
-- statement:
--   The group-theoretic branching budget bounds every finite prefix set.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L86-L101
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L86-L101

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.livePaths_prefix_bound [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) (n : ℕ) :
    (FinitePaths.initialSegment n '' livePaths f).ncard ≤ pathWeight f [] := by sorry

-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_liveDescendants_ncard_le
-- name    : Kourovka.ProductPaths.liveDescendants_ncard_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:29.376087+00:00
-- url     : https://prove2.me/theorems/d3dc88b1-855a-4f2f-8eb9-4ace26f324a5
-- title:
--   Product Paths: live Descendants ncard le
-- statement:
--   The number of nonabelian leaves is uniformly bounded by the root's finite budget.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L45-L75
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L45-L75

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.liveDescendants_ncard_le [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) (n : ℕ) :
    ∀ w, (liveDescendants f w n).ncard ≤ pathWeight f w := by sorry

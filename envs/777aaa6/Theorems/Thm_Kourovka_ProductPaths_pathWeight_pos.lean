-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_pathWeight_pos
-- name    : Kourovka.ProductPaths.pathWeight_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:55.97417+00:00
-- url     : https://prove2.me/theorems/acb43b62-85f1-4903-86bf-2ea0b44b7364
-- title:
--   Product Paths: path Weight pos
-- statement:
--   A nonabelian path uses at least one unit of the finite budget.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathWeight.lean#L75-L82
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathWeight.lean#L75-L82

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_Paths
import Definitions.Def_Kourovka_PathWeight
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.pathWeight_pos [Group.FG A] [Group.FG B] [IsSolvable A] [IsSolvable B]
    (f : A × B →* A × B) (w : List Bool) (h : Nonabelian f w) :
    0 < pathWeight f w := by sorry

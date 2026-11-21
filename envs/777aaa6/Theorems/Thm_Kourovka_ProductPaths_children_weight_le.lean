-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_children_weight_le
-- name    : Kourovka.ProductPaths.children_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:04.266379+00:00
-- url     : https://prove2.me/theorems/0273b6be-a452-4673-a89d-a68c715f403f
-- title:
--   Product Paths: children weight le
-- statement:
--   The finite budget splits between the two children of every path.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathWeight.lean#L65-L72
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathWeight.lean#L65-L72

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_Paths
import Definitions.Def_Kourovka_PathWeight
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.children_weight_le [Group.FG A] [Group.FG B]
    (f : A × B →* A × B) (hf : Function.Surjective f) (w : List Bool) :
    pathWeight f (w ++ [false]) + pathWeight f (w ++ [true]) ≤ pathWeight f w := by sorry

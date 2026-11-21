-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_pathWeight_nil
-- name    : Kourovka.ProductPaths.pathWeight_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:55.75027+00:00
-- url     : https://prove2.me/theorems/6dba4d69-9676-4798-a3b7-0afbafd727eb
-- title:
--   Product Paths: path Weight nil
-- statement:
--   The root budget is an invariant of the product, independent of the endomorphism.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathWeight.lean#L59-L62
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathWeight.lean#L59-L62

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_Paths
import Definitions.Def_Kourovka_PathWeight
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.pathWeight_nil (f : A × B →* A × B) :
    pathWeight f [] = CenterWeight.weight (A × B) := by sorry

-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_map_mk_of_perm
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.map_mk_of_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:16:30.255477+00:00
-- url     : https://prove2.me/theorems/d8fc35c1-eb01-4857-b675-1d4918050fec
-- title:
--   Schreier Heights: map mk of perm
-- statement:
--   The Schreier Heights construction uses the map mk of perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierHeights.lean#L43-L47
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierHeights.lean#L43-L47

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
import Definitions.Def_Kourovka_Schreier_PathLifting
import Definitions.Def_Kourovka_Halfspaces_SchreierHeights
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X Q : Type*} [CommGroup Q]

theorem Kourovka.MetabelianEnumeration.SchreierHeights.map_mk_of_perm (π : FreeGroup X →* Q) {xs ys : List (X × Bool)}
    (h : xs.Perm ys) : π (FreeGroup.mk xs) = π (FreeGroup.mk ys) := by sorry

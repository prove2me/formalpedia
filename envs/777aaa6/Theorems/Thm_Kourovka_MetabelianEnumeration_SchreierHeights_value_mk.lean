-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_value_mk
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.value_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:16:26.767556+00:00
-- url     : https://prove2.me/theorems/273432e6-91ec-4c3b-9000-7c99b5ef2c9a
-- title:
--   Schreier Heights: value mk
-- statement:
--   The Schreier Heights construction uses the value mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierHeights.lean#L35-L41
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierHeights.lean#L35-L41

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

theorem Kourovka.MetabelianEnumeration.SchreierHeights.value_mk (θ : FreeGroup X →* Multiplicative ℝ) (xs : List (X × Bool)) :
    value θ (FreeGroup.mk xs) = (xs.map (letterHeight fun x => value θ (FreeGroup.of x))).sum := by sorry

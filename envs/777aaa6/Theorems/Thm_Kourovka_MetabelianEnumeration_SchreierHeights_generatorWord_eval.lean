-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_generatorWord_eval
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.generatorWord_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:20:39.412189+00:00
-- url     : https://prove2.me/theorems/1ace7f1a-1c98-4ca5-b901-44a20e0c2e7d
-- title:
--   Schreier Heights: generator Word eval
-- statement:
--   The Schreier Heights construction uses the generator Word eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierPaths.lean#L58-L62
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierPaths.lean#L58-L62

import Definitions.Def_Kourovka_Halfspaces_SchreierKernel
import Definitions.Def_Kourovka_Halfspaces_SchreierPaths
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X : Type*}

theorem Kourovka.MetabelianEnumeration.SchreierHeights.generatorWord_eval [DecidableEq X] {L : Subgroup (FreeGroup X)}
    (S : Transversal L) (z : S.Edge) :
    FreeGroup.mk (generatorWord S z) = S.edgeValue z := by sorry

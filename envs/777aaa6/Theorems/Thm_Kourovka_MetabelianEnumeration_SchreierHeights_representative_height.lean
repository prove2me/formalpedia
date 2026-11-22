-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_representative_height
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.representative_height
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:16:41.76332+00:00
-- url     : https://prove2.me/theorems/308be8a8-f5b4-49a9-841e-994837e5d972
-- title:
--   Schreier Heights: representative height
-- statement:
--   The Schreier Heights construction uses the representative height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierHeights.lean#L97-L104
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierHeights.lean#L97-L104

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

theorem Kourovka.MetabelianEnumeration.SchreierHeights.representative_height (π : FreeGroup X →* Q) (χ : Q →* Multiplicative ℝ)
    (S : Transversal π.ker) (w : FreeGroup X) :
    value (χ.comp π) (S.rep w) = value (χ.comp π) w := by sorry

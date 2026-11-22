-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_rewrite_mem_closure
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.rewrite_mem_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:16:41.262628+00:00
-- url     : https://prove2.me/theorems/3516fa31-e4b6-4061-8384-1255fcdd9969
-- title:
--   Schreier Heights: rewrite mem closure
-- statement:
--   Rewriting a path confined to a height region uses only symbols of that
--   region. This includes the literal negative-letter Schreier convention.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierHeights.lean#L114-L149
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierHeights.lean#L114-L149

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

theorem Kourovka.MetabelianEnumeration.SchreierHeights.rewrite_mem_closure (π : FreeGroup X →* Q) (χ : Q →* Multiplicative ℝ)
    (S : Transversal π.ker) (P : ℝ → Prop)
    (p : FreeGroup X) (xs : List (X × Bool))
    (hpath : PathIn (letterHeight fun x => value (χ.comp π) (FreeGroup.of x)) P
      (value (χ.comp π) p) xs) :
    S.rewriteWord p xs ∈
      Subgroup.closure (FreeGroup.of '' symbolsIn (χ.comp π) S P) := by sorry

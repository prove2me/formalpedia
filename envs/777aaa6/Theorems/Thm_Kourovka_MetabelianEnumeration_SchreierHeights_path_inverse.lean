-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_path_inverse
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.path_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:20:33.029509+00:00
-- url     : https://prove2.me/theorems/a42b5442-130f-42a3-80d6-31b0fd5a5f42
-- title:
--   Schreier Heights: path inverse
-- statement:
--   The Schreier Heights construction uses the path inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierPaths.lean#L24-L40
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierPaths.lean#L24-L40

import Definitions.Def_Kourovka_Halfspaces_SchreierKernel
import Definitions.Def_Kourovka_Halfspaces_SchreierPaths
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X : Type*}

theorem Kourovka.MetabelianEnumeration.SchreierHeights.path_inverse (θ : FreeGroup X →* Multiplicative ℝ) (P : ℝ → Prop)
    (p : ℝ) (xs : List (X × Bool)) (h : PathIn (step θ) P p xs) :
    PathIn (step θ) P (p + value θ (FreeGroup.mk xs)) (FreeGroup.invRev xs) := by sorry

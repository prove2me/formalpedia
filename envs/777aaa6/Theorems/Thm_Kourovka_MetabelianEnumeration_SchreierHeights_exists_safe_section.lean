-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_exists_safe_section
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.exists_safe_section
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:16:45.064723+00:00
-- url     : https://prove2.me/theorems/fca52993-365f-4167-aa44-80d2a7a2d39f
-- title:
--   Schreier Heights: exists safe section
-- statement:
--   A section of the quotient map, chosen with paths in the correct halfspace;
--   representatives of overlap vertices stay inside the overlap.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierHeights.lean#L51-L81
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierHeights.lean#L51-L81

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

theorem Kourovka.MetabelianEnumeration.SchreierHeights.exists_safe_section [DecidableEq X] (π : FreeGroup X →* Q)
    (hπ : Function.Surjective π) (χ : Q →* Multiplicative ℝ)
    (D μ : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ x, |value (χ.comp π) (FreeGroup.of x)| ≤ D) (hμ : 2 * D ≤ μ) :
    ∃ r : Q → FreeGroup X, (∀ q, π (r q) = q) ∧ r 1 = 1 ∧
      ∀ q, PathIn (letterHeight fun x => value (χ.comp π) (FreeGroup.of x))
        (fun z => min 0 (χ q).toAdd ≤ z ∧ z ≤ max μ (χ q).toAdd) 0 (r q).toWord := by sorry

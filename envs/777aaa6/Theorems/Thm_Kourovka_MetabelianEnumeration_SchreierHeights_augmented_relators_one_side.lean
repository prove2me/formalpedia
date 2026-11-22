-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_augmented_relators_one_side
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.augmented_relators_one_side
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:19:20.126269+00:00
-- url     : https://prove2.me/theorems/4af71852-8eb9-4f5d-a93d-4abd9df9b961
-- title:
--   Schreier Heights: augmented relators one side
-- statement:
--   Lifted defining relators and section-path relators are each confined
--   to one of the two overlapping halfspaces.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceRelators.lean#L60-L114
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceRelators.lean#L60-L114

import Definitions.Def_Kourovka_Halfspaces_SchreierHeights
import Definitions.Def_Kourovka_Schreier_KernelPresentation
import Definitions.Def_Kourovka_Halfspaces_HalfspaceRelators
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X Q : Type*} [CommGroup Q]

theorem Kourovka.MetabelianEnumeration.SchreierHeights.augmented_relators_one_side [DecidableEq X]
    (π : FreeGroup X →* Q) (χ : Q →* Multiplicative ℝ)
    (S : Transversal π.ker) (R : Set (FreeGroup X))
    (D B μ : ℝ) (hD0 : 0 ≤ D) (hDB : D ≤ B) (hμ : 2 * B ≤ μ)
    (hD : ∀ x, |value (χ.comp π) (FreeGroup.of x)| ≤ D)
    (hR : ∀ r ∈ R, (r.toWord.length : ℝ) * D ≤ B)
    (hsafe : ∀ t : S.vertices,
      PathIn (letterHeight fun x => value (χ.comp π) (FreeGroup.of x))
        (fun z => min 0 (value (χ.comp π) t.val) ≤ z ∧
          z ≤ max μ (value (χ.comp π) t.val)) 0 t.val.toWord)
    (r : FreeGroup (S.Edge))
    (hr : r ∈ S.relators R) :
    r ∈ Subgroup.closure (FreeGroup.of '' symbolsIn (χ.comp π) S (fun z => 0 ≤ z)) ∨
      r ∈ Subgroup.closure (FreeGroup.of '' symbolsIn (χ.comp π) S (fun z => z ≤ μ)) := by sorry

-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_finite_presentation_halfspace_generation
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.finite_presentation_halfspace_generation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:22:12.163167+00:00
-- url     : https://prove2.me/theorems/a567f159-b3db-46fe-b559-299e3cdeea98
-- title:
--   Schreier Heights: finite presentation halfspace generation
-- statement:
--   Unconditional halfspace splitting for an actual finite ordinary
--   presentation with abelian kernel and abelian quotient.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeneration.lean#L104-L142
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeneration.lean#L104-L142

import Definitions.Def_Kourovka_Halfspaces_SchreierPaths
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry HalfspaceSplitting HalfspaceLoops
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X L : Type} [AddCommGroup L] [DecidableEq X]

theorem Kourovka.MetabelianEnumeration.SchreierHeights.finite_presentation_halfspace_generation [Fintype X]
    (R : Set (FreeGroup X)) (hRfinite : R.Finite)
    (π : PresentedGroup R →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (habelian : ∀ a b : π.ker, Commute a b) :
    ∃ μ : ℝ, 0 ≤ μ ∧
      (Subgroup.closure (loopSet π χ PresentedGroup.of (fun z => 0 ≤ z)) = ⊤ ∨
        Subgroup.closure (loopSet π χ PresentedGroup.of (fun z => z ≤ μ)) = ⊤) := by sorry

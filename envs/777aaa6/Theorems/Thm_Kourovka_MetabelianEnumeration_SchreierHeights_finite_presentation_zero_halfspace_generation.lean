-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_finite_presentation_zero_halfspace_generation
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.finite_presentation_zero_halfspace_generation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:22:44.46149+00:00
-- url     : https://prove2.me/theorems/0a751539-1ad6-40ee-8314-8d79726efc38
-- title:
--   Schreier Heights: finite presentation zero halfspace generation
-- statement:
--   Both halfspaces are based at zero; the cutoff is removed by conjugation,
--   using the nonzero character and the actual finite generating alphabet.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceShift.lean#L119-L127
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceShift.lean#L119-L127

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry HalfspaceLoops
open Kourovka.Schreier.Transversal
variable {X L : Type} [AddCommGroup L] [DecidableEq X]

theorem Kourovka.MetabelianEnumeration.SchreierHeights.finite_presentation_zero_halfspace_generation [Fintype X]
    (R : Set (FreeGroup X)) (hRfinite : R.Finite)
    (π : PresentedGroup R →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (habelian : ∀ a b : π.ker, Commute a b) :
    Subgroup.closure (loopSet π χ PresentedGroup.of (fun z => 0 ≤ z)) = ⊤ ∨
      Subgroup.closure (loopSet π χ PresentedGroup.of (fun z => z ≤ 0)) = ⊤ := by sorry

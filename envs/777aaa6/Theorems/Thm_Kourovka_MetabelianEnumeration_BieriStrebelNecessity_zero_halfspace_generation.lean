-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_BieriStrebelNecessity_zero_halfspace_generation
-- name    : Kourovka.MetabelianEnumeration.BieriStrebelNecessity.zero_halfspace_generation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:23:29.104643+00:00
-- url     : https://prove2.me/theorems/69015d9a-29fe-4bd8-8e17-c81deb451f2f
-- title:
--   Bieri Strebel Necessity: zero halfspace generation
-- statement:
--   The halfspace-generation conclusion is invariant under the chosen finite
--   ordinary presentation of the group.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/BieriStrebelNecessity.lean#L80-L97
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/BieriStrebelNecessity.lean#L80-L97

import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Definitions.Def_Kourovka_Halfspaces_BieriStrebelNecessity
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.BieriStrebelNecessity
open HalfspaceGeometry HalfspaceLoops SchreierHeights ValuationModule
open CommutatorModule SignedTameness
variable {X E L : Type} [Group E] [AddCommGroup L]

theorem Kourovka.MetabelianEnumeration.BieriStrebelNecessity.zero_halfspace_generation [DecidableEq X] [Fintype X]
    (R : Set (FreeGroup X)) (hR : R.Finite) (e : PresentedGroup R ≃* E)
    (π : E →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (hχ : χ ≠ 0) [IsMulCommutative π.ker] :
    Subgroup.closure (loopSet π χ (fun x : X => e (PresentedGroup.of x)) (fun z => 0 ≤ z)) = ⊤ ∨
      Subgroup.closure (loopSet π χ (fun x : X => e (PresentedGroup.of x)) (fun z => z ≤ 0)) = ⊤ := by sorry

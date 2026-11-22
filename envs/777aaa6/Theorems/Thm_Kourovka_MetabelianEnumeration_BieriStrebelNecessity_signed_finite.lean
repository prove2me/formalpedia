-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_BieriStrebelNecessity_signed_finite
-- name    : Kourovka.MetabelianEnumeration.BieriStrebelNecessity.signed_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:23:47.287173+00:00
-- url     : https://prove2.me/theorems/db314de8-1a12-421c-96a1-dcd731188399
-- title:
--   Bieri Strebel Necessity: signed finite
-- statement:
--   Genuine finite presentation implies directional finiteness on at least
--   one side of every nonzero character for the actual Laurent conjugation action.
--   The full-ring finite-generation input is independently obtained from finite
--   normal kernel generators.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/BieriStrebelNecessity.lean#L103-L118
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/BieriStrebelNecessity.lean#L103-L118

import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Definitions.Def_Kourovka_Halfspaces_BieriStrebelNecessity
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.BieriStrebelNecessity
open HalfspaceGeometry HalfspaceLoops SchreierHeights ValuationModule
open CommutatorModule SignedTameness
variable {X E L : Type} [Group E] [AddCommGroup L]

theorem Kourovka.MetabelianEnumeration.BieriStrebelNecessity.signed_finite [DecidableEq X] [Fintype X] [DecidableEq L]
    (R : Set (FreeGroup X)) (hR : R.Finite) (e : PresentedGroup R ≃* E)
    (π : E →* Multiplicative L) (hπ : Function.Surjective π)
    [IsMulCommutative π.ker] (χ : L →+ ℝ) (hχ : χ ≠ 0) :
    letI := laurentModule π hπ (MonoidHom.id (Multiplicative L))
    Module.Finite (GroupRing L) (Additive π.ker) →
    Module.Finite (nonnegativeRing χ) (Additive π.ker) ∨
      Module.Finite (nonnegativeRing (-χ)) (Additive π.ker) := by sorry

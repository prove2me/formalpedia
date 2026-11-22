-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_BieriStrebelNecessity_tame_of_finite_presentation
-- name    : Kourovka.MetabelianEnumeration.BieriStrebelNecessity.tame_of_finite_presentation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:23:49.86411+00:00
-- url     : https://prove2.me/theorems/5eb68642-8a01-4334-8f21-2d3bd7315b0a
-- title:
--   Bieri Strebel Necessity: tame of finite presentation
-- statement:
--   The actual Bieri–Strebel tameness property for a lattice quotient.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/BieriStrebelNecessity.lean#L121-L130
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/BieriStrebelNecessity.lean#L121-L130

import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Definitions.Def_Kourovka_Halfspaces_BieriStrebelNecessity
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.BieriStrebelNecessity
open HalfspaceGeometry HalfspaceLoops SchreierHeights ValuationModule
open CommutatorModule SignedTameness
variable {X E L : Type} [Group E] [AddCommGroup L]

theorem Kourovka.MetabelianEnumeration.BieriStrebelNecessity.tame_of_finite_presentation {k : ℕ} [DecidableEq X] [Fintype X]
    (R : Set (FreeGroup X)) (hR : R.Finite) (e : PresentedGroup R ≃* E)
    (π : E →* Multiplicative (FiniteCover.Lattice k)) (hπ : Function.Surjective π)
    [IsMulCommutative π.ker] :
    letI := laurentModule π hπ (MonoidHom.id (Multiplicative (FiniteCover.Lattice k)))
    Module.Finite (GroupRing (FiniteCover.Lattice k)) (Additive π.ker) →
      Tame (k := k) (Additive π.ker) := by sorry

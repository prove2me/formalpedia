-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.BieriStrebelNecessity.tame_of_finite_presentation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:30:59.072843+00:00
-- url     : https://prove2.me/submissions/ee5f3712-4ea0-4c95-8da1-0e27a765c3d3

import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Definitions.Def_Kourovka_Halfspaces_BieriStrebelNecessity
import Theorems.Thm_Kourovka_MetabelianEnumeration_BieriStrebelNecessity_signed_finite
import Theorems.Thm_Kourovka_MetabelianEnumeration_SignedTameness_character_ne_zero


set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.BieriStrebelNecessity
open HalfspaceGeometry HalfspaceLoops SchreierHeights ValuationModule
open CommutatorModule SignedTameness
variable {X E L : Type} [Group E] [AddCommGroup L]
namespace Kourovka.MetabelianEnumeration.BieriStrebelNecessity
theorem _root_.solution {k : ℕ} [DecidableEq X] [Fintype X]
    (R : Set (FreeGroup X)) (hR : R.Finite) (e : PresentedGroup R ≃* E)
    (π : E →* Multiplicative (FiniteCover.Lattice k)) (hπ : Function.Surjective π)
    [IsMulCommutative π.ker] :
    letI := laurentModule π hπ (MonoidHom.id (Multiplicative (FiniteCover.Lattice k)))
    Module.Finite (GroupRing (FiniteCover.Lattice k)) (Additive π.ker) →
      Tame (k := k) (Additive π.ker) := by
  letI := laurentModule π hπ (MonoidHom.id (Multiplicative (FiniteCover.Lattice k)))
  intro hf x hx
  exact signed_finite R hR e π hπ (character x) (character_ne_zero hx) hf
end Kourovka.MetabelianEnumeration.BieriStrebelNecessity

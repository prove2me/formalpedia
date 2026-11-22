-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CommutatorModule.quotientConjugation_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:05.132243+00:00
-- url     : https://prove2.me/submissions/a2553b0a-79a3-4821-9b26-481f231f30f1

import Definitions.Def_Kourovka_Presentations_PullbackPresentation
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Definitions.Def_Kourovka_Modules_CommutatorModule

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {α : Type} [Fintype α]
variable {E Q : Type} [Group E] [CommGroup Q]
variable (π : E →* Q) (hπ : Function.Surjective π) [IsMulCommutative π.ker]
namespace Kourovka.MetabelianEnumeration.CommutatorModule
theorem _root_.solution (g : E) :
    quotientConjugation π hπ (π g) = MulAut.conjNormal g := by
  have h := (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm_apply_apply
    (QuotientGroup.mk g)
  change (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π g) =
    QuotientGroup.mk g at h
  change QuotientGroup.lift π.ker (MulAut.conjNormal (H := π.ker))
    (kernel_le_conjugation_kernel π)
    ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π g)) = _
  rw [h]
  rfl
end Kourovka.MetabelianEnumeration.CommutatorModule

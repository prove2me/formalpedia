-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CommutatorModule.rightRepresentation_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:18:28.907348+00:00
-- url     : https://prove2.me/submissions/767ec336-d395-42a3-bb33-30ea9b308c23

import Definitions.Def_Kourovka_Presentations_PullbackPresentation
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Definitions.Def_Kourovka_Modules_CommutatorModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_rightConjugation_image

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {α : Type} [Fintype α]
variable {E Q : Type} [Group E] [CommGroup Q]
variable (π : E →* Q) (hπ : Function.Surjective π) [IsMulCommutative π.ker]
namespace Kourovka.MetabelianEnumeration.CommutatorModule
theorem _root_.solution (g : E) (a : Additive π.ker) :
    (rightRepresentation π hπ (π g) a).toMul.val = g⁻¹ * a.toMul.val * g :=
  rightConjugation_image π hπ g a.toMul
end Kourovka.MetabelianEnumeration.CommutatorModule

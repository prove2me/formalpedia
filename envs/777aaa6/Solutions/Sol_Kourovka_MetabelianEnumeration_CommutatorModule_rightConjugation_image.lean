-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CommutatorModule.rightConjugation_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:51.232179+00:00
-- url     : https://prove2.me/submissions/e95a320b-cdc8-41eb-8cef-550a3c78f1a6

import Definitions.Def_Kourovka_Presentations_PullbackPresentation
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Definitions.Def_Kourovka_Modules_CommutatorModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_quotientConjugation_image

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {α : Type} [Fintype α]
variable {E Q : Type} [Group E] [CommGroup Q]
variable (π : E →* Q) (hπ : Function.Surjective π) [IsMulCommutative π.ker]
namespace Kourovka.MetabelianEnumeration.CommutatorModule
theorem _root_.solution (g : E) (a : π.ker) :
    (rightConjugation π hπ (π g) a).val = g⁻¹ * a.val * g := by
  change (quotientConjugation π hπ ((π g)⁻¹) a).val = _
  rw [← map_inv, quotientConjugation_image, MulAut.conjNormal_apply, inv_inv]
end Kourovka.MetabelianEnumeration.CommutatorModule

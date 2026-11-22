-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CommutatorModule.laurent_single_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:02.191905+00:00
-- url     : https://prove2.me/submissions/bb27517a-96d8-49fc-8432-d22a4a835a0b

import Definitions.Def_Kourovka_Modules_CommutatorModule
import Definitions.Def_Kourovka_Modules_LaurentAction
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_laurent_single
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_rightConjugation_image


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {E Q L : Type} [Group E] [CommGroup Q] [AddCommGroup L]
variable (π : E →* Q) (hπ : Function.Surjective π) [IsMulCommutative π.ker]
variable (q : Multiplicative L →* Q)
namespace Kourovka.MetabelianEnumeration.CommutatorModule
theorem _root_.solution (u : L) (g : E)
    (hu : q (Multiplicative.ofAdd u) = π g) (a : Additive π.ker) :
    letI := laurentModule π hπ q
    (((AddMonoidAlgebra.single u 1 : AddMonoidAlgebra ℤ L) • a) : Additive π.ker).toMul.val =
      g⁻¹ * a.toMul.val * g := by
  letI := laurentModule π hπ q
  rw [laurent_single, hu]
  exact rightConjugation_image π hπ g a.toMul
end Kourovka.MetabelianEnumeration.CommutatorModule

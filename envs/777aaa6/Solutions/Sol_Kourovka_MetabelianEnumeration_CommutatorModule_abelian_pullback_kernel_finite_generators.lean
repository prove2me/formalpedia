-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CommutatorModule.abelian_pullback_kernel_finite_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:18:29.794249+00:00
-- url     : https://prove2.me/submissions/ae9e725f-3178-46d1-a744-6058b3445646

import Definitions.Def_Kourovka_Modules_CommutatorModule
import Definitions.Def_Kourovka_Presentations_KernelGenerators
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_finite_normal_generators_of_kernel_equiv
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_abelianQuotientMap_surjective
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_first_surjective
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_commutator_finite_normal_generators


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {E G : Type} [Group E] [Group G]
namespace Kourovka.MetabelianEnumeration.CommutatorModule
theorem _root_.solution {α : Type} [Fintype α]
    (R : List (FreeGroup α)) :
    ∃ s : Finset (CofinalCover.second Abelianization.of
      (CofinalCover.abelianQuotientMap R)).ker,
      Subgroup.normalClosure (Subtype.val '' (s : Set (CofinalCover.second Abelianization.of
        (CofinalCover.abelianQuotientMap R)).ker)) =
        (CofinalCover.second Abelianization.of (CofinalCover.abelianQuotientMap R)).ker := by
  apply finite_normal_generators_of_kernel_equiv
    (CofinalCover.first Abelianization.of (CofinalCover.abelianQuotientMap R))
    (CofinalCover.first_surjective _ _ (CofinalCover.abelianQuotientMap_surjective R)) _
    (Abelianization.of (G := PresentedGroup (CentralExtension.relSet R))).ker
    (CofinalCover.secondKernelEquiv _ _)
  · intro x
    rfl
  · rw [Abelianization.ker_of]
    exact commutator_finite_normal_generators R
end Kourovka.MetabelianEnumeration.CommutatorModule

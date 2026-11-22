-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.lattice_kernel_finite_normal_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:45.223766+00:00
-- url     : https://prove2.me/submissions/bb829b85-3b8a-437c-ac94-8ec67c3f4b90

import Definitions.Def_Kourovka_Presentations_KernelGenerators
import Definitions.Def_Kourovka_Modules_LaurentAction
import Definitions.Def_Kourovka_Covers_FiniteCover
import Definitions.Def_Kourovka_Cofinality_LatticePullback
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_abelianQuotientMap_surjective
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_first_surjective
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_commutator_finite_normal_generators
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_finite_normal_generators_of_kernel_equiv


set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
open FiniteCover CommutatorModule
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution {k : ℕ} (R : List (FreeGroup (Fin k))) :
    ∃ s : Finset (latticeProjection R).ker,
      Subgroup.normalClosure (Subtype.val '' (s : Set (latticeProjection R).ker)) =
        (latticeProjection R).ker := by
  let e := (latticeKernelEquiv R).trans
    (secondKernelEquiv Abelianization.of (abelianQuotientMap R))
  apply finite_normal_generators_of_kernel_equiv
    (first Abelianization.of (abelianQuotientMap R))
    (first_surjective _ _ (abelianQuotientMap_surjective R)) _
    (Abelianization.of (G := PresentedGroup (CentralExtension.relSet R))).ker e
  · intro x
    rfl
  · rw [Abelianization.ker_of]
    exact commutator_finite_normal_generators R
end Kourovka.MetabelianEnumeration.CofinalCover

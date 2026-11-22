-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CommutatorModule.abelian_kernel_commutative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:51.687341+00:00
-- url     : https://prove2.me/submissions/61bf6a75-2783-4d35-9572-7267a7ea8922

import Definitions.Def_Kourovka_Modules_CommutatorModule
import Definitions.Def_Kourovka_Presentations_KernelGenerators
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_commutator_commutative


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {E G : Type} [Group E] [Group G]
namespace Kourovka.MetabelianEnumeration.CommutatorModule
theorem _root_.solution (hG : Metabelian G) :
    IsMulCommutative (Abelianization.of (G := G)).ker := by
  letI := commutator_commutative hG
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  have hx : x.val ∈ commutator G := by
    rw [← Abelianization.ker_of]
    exact x.property
  have hy : y.val ∈ commutator G := by
    rw [← Abelianization.ker_of]
    exact y.property
  exact congrArg (fun z : commutator G => z.val)
    (mul_comm (⟨x.val, hx⟩ : commutator G) (⟨y.val, hy⟩ : commutator G))
end Kourovka.MetabelianEnumeration.CommutatorModule

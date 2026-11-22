-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_finite_normal_generators_of_kernel_equiv
-- name    : Kourovka.MetabelianEnumeration.CommutatorModule.finite_normal_generators_of_kernel_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:14.297413+00:00
-- url     : https://prove2.me/theorems/16ce9bf8-fbdd-4e86-9d19-5c472db1250e
-- title:
--   Commutator Module: finite normal generators of kernel equiv
-- statement:
--   The Commutator Module construction uses the finite normal generators of kernel equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/KernelGenerators.lean#L18-L62
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/KernelGenerators.lean#L18-L62

import Definitions.Def_Kourovka_Modules_CommutatorModule
import Definitions.Def_Kourovka_Presentations_KernelGenerators
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {E G : Type} [Group E] [Group G]

theorem Kourovka.MetabelianEnumeration.CommutatorModule.finite_normal_generators_of_kernel_equiv
    (f : E →* G) (hf : Function.Surjective f)
    (N : Subgroup E) [N.Normal] (M : Subgroup G) [M.Normal]
    (e : N ≃* M) (he : ∀ x : N, f x.val = (e x).val)
    (hM : ∃ s : Finset G, Subgroup.normalClosure (s : Set G) = M) :
    ∃ s : Finset N, Subgroup.normalClosure (Subtype.val '' (s : Set N)) = N := by sorry

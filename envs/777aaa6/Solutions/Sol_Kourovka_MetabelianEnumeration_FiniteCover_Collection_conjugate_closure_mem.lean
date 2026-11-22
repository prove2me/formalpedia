-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_closure_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:21.760878+00:00
-- url     : https://prove2.me/submissions/33ac19bc-30f0-4cc4-b0e2-ee24e3af0501

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution (S : Set G) (g : G)
    (h : ∀ x ∈ S, conjugate x g ∈ Subgroup.closure S) :
    ∀ x ∈ Subgroup.closure S, conjugate x g ∈ Subgroup.closure S := by
  have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj g⁻¹).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simpa [Subgroup.mem_comap, MulAut.conj_apply, conjugate] using h x hx
  intro x hx
  simpa [Subgroup.mem_comap, MulAut.conj_apply, conjugate] using hle hx
end Kourovka.MetabelianEnumeration.FiniteCover.Collection

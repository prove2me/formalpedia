-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.mem_normalizer_of_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:22.447196+00:00
-- url     : https://prove2.me/submissions/2060431a-aad6-417a-968e-8137e3d31ba6

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
theorem _root_.solution {H : Subgroup G} {g : G}
    (hg : ∀ x ∈ H, conjugate x g ∈ H)
    (hi : ∀ x ∈ H, conjugate x g⁻¹ ∈ H) : g ∈ H.normalizer := by
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  constructor
  · exact hg x
  · intro hx
    have hh := hi (conjugate x g) hx
    simpa [conjugate, mul_assoc] using hh
end Kourovka.MetabelianEnumeration.FiniteCover.Collection

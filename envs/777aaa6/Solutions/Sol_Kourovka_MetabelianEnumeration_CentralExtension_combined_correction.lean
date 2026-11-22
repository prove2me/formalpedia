-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CentralExtension.combined_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:08:55.783045+00:00
-- url     : https://prove2.me/submissions/cf81fb8d-8cf0-4cd7-965b-dc800641b145

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_Kourovka_Presentations_CentralExtension

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CentralExtension
variable {α β : Type} [Fintype α] [Fintype β]
namespace Kourovka.MetabelianEnumeration.CentralExtension
theorem _root_.solution (R : List (FreeGroup α)) (S : List (FreeGroup β))
    (c : FreeGroup α → FreeGroup β) (r : FreeGroup α) (hr : r ∈ R) :
    PresentedGroup.mk (relSet (combinedRelations R S c)) (FreeGroup.map Sum.inl r) =
      PresentedGroup.mk (relSet (combinedRelations R S c)) (FreeGroup.map Sum.inr (c r)) := by
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  simp only [relSet, Set.mem_setOf_eq, combinedRelations, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl ⟨r, hr, rfl⟩)
end Kourovka.MetabelianEnumeration.CentralExtension

-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CommutatorModule.commutator_finite_normal_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:57:09.71418+00:00
-- url     : https://prove2.me/submissions/d0a2ba4a-1268-4e96-b9eb-da196d8a5862

import Definitions.Def_Kourovka_Presentations_PullbackPresentation
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Definitions.Def_Kourovka_Modules_CommutatorModule

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {α : Type} [Fintype α]
namespace Kourovka.MetabelianEnumeration.CommutatorModule
theorem _root_.solution (R : List (FreeGroup α)) :
    ∃ s : Finset (PresentedGroup (CentralExtension.relSet R)),
      Subgroup.normalClosure (s : Set (PresentedGroup (CentralExtension.relSet R))) =
        commutator (PresentedGroup (CentralExtension.relSet R)) := by
  classical
  let f := PresentedGroup.mk (CentralExtension.relSet R)
  let S := (CentralExtension.abelianRelations α).map f
  refine ⟨S.toFinset, ?_⟩
  have himage : f '' CentralExtension.relSet (CentralExtension.abelianRelations α) =
      (S.toFinset : Set (PresentedGroup (CentralExtension.relSet R))) := by
    ext x
    simp only [Set.mem_image, CentralExtension.relSet, Set.mem_setOf_eq,
      Finset.mem_coe, List.mem_toFinset, S, List.mem_map]
  have hsurj := PresentedGroup.mk_surjective (CentralExtension.relSet R)
  rw [← himage, ← Subgroup.map_normalClosure _ f hsurj,
    CentralExtension.abelian_relations_normalClosure, map_commutator_eq,
    MonoidHom.range_eq_top.mpr hsurj]
  rfl
end Kourovka.MetabelianEnumeration.CommutatorModule

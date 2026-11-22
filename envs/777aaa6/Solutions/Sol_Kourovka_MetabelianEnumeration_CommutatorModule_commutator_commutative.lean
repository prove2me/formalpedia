-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CommutatorModule.commutator_commutative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:04.679429+00:00
-- url     : https://prove2.me/submissions/8f39e85a-66b1-4356-8c71-0d1bcf561772

import Definitions.Def_Kourovka_Presentations_PullbackPresentation
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Definitions.Def_Kourovka_Modules_CommutatorModule

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {α : Type} [Fintype α]
namespace Kourovka.MetabelianEnumeration.CommutatorModule
theorem _root_.solution {G : Type} [Group G] (hG : Metabelian G) :
    IsMulCommutative (commutator G) := by
  let C := Subgroup.closure (commutatorSet G)
  letI : CommGroup C := Subgroup.closureCommGroupOfComm (by
    rintro x ⟨a, b, rfl⟩ y ⟨c, d, rfl⟩
    exact (hG a b c d).eq)
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  have hx : x.val ∈ C := by
    change x.val ∈ Subgroup.closure (commutatorSet G)
    rw [← commutator_eq_closure]
    exact x.property
  have hy : y.val ∈ C := by
    change y.val ∈ Subgroup.closure (commutatorSet G)
    rw [← commutator_eq_closure]
    exact y.property
  exact congrArg (fun z : C => z.val) (mul_comm (⟨x.val, hx⟩ : C) (⟨y.val, hy⟩ : C))
end Kourovka.MetabelianEnumeration.CommutatorModule

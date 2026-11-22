-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:44:43.663109+00:00
-- url     : https://prove2.me/submissions/36b5b952-d9b4-46b4-b771-87da51011744

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution (x u v : G) :
    conjugate x (u * v) = conjugate (conjugate x u) v := by
  simp [conjugate, mul_assoc]
end Kourovka.MetabelianEnumeration.FiniteCover.Collection

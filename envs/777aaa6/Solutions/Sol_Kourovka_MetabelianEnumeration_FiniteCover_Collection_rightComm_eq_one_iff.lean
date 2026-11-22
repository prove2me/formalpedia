-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.rightComm_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:53:35.281533+00:00
-- url     : https://prove2.me/submissions/0109149f-e140-409c-b4f7-624ac9beca7c

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
theorem _root_.solution (x y : G) : rightComm x y = 1 ↔ Commute x y := by
  constructor
  · intro h
    change x * y = y * x
    have hh := congrArg (fun z => y * x * z) h
    simpa [rightComm, mul_assoc] using hh
  · intro h
    change x⁻¹ * y⁻¹ * x * y = 1
    rw [mul_assoc, mul_assoc, h.eq]
    group
end Kourovka.MetabelianEnumeration.FiniteCover.Collection

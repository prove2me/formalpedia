-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceLoops.conjugate_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:47.161482+00:00
-- url     : https://prove2.me/submissions/16091c56-be6b-4cfa-900f-7de33396486e

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_one
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.difference_one

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceLoops
open HalfspaceGeometry HalfspaceModule ValuationModule
variable {E L X : Type} [Group E] [AddCommGroup L]
variable (π : E →* Multiplicative L)
variable [IsMulCommutative π.ker]
omit [IsMulCommutative ↥π.ker]
namespace Kourovka.MetabelianEnumeration.HalfspaceLoops
theorem _root_.solution (p x : E) (n : Additive π.ker) :
    conjugate π p (conjugate π x n) = conjugate π (p * x) n := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change p * (x * n.toMul.val * x⁻¹) * p⁻¹ =
    (p * x) * n.toMul.val * (p * x)⁻¹
  group
end Kourovka.MetabelianEnumeration.HalfspaceLoops

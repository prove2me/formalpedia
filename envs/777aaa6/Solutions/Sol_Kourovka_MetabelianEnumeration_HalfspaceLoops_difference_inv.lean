-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceLoops.difference_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:13.422778+00:00
-- url     : https://prove2.me/submissions/cacb3bd7-5f15-4b67-a3eb-5135417fed2e

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
theorem _root_.solution (u x : E) :
    difference π u x⁻¹ = -conjugate π x⁻¹ (difference π u x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ⁅u, x⁻¹⁆ = (x⁻¹ * ⁅u, x⁆ * (x⁻¹)⁻¹)⁻¹
  group
end Kourovka.MetabelianEnumeration.HalfspaceLoops

-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceLoops.difference_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:06.255194+00:00
-- url     : https://prove2.me/submissions/5dce0890-fdd3-40df-8167-8745ec66894a

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
theorem _root_.solution (u p x : E) :
    difference π u (p * x) = difference π u p + conjugate π p (difference π u x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ⁅u, p * x⁆ = ⁅u, p⁆ * (p * ⁅u, x⁆ * p⁻¹)
  group
end Kourovka.MetabelianEnumeration.HalfspaceLoops

-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceLoops.height_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:50:59.789336+00:00
-- url     : https://prove2.me/submissions/294b3075-4192-4ae6-ac6e-e6e33b3416f8

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
theorem _root_.solution (χ : L →+ ℝ) : height π χ 1 = 0 := by
  simp [height]
end Kourovka.MetabelianEnumeration.HalfspaceLoops

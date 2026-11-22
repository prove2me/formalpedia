-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceLoops.height_letter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:58:26.317971+00:00
-- url     : https://prove2.me/submissions/00d23620-5184-4ef9-bcf5-aeef587d00ad

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_inv
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_cons
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.difference_one
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_one
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_mul
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_inv
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.evalWord_nil
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.evalWord_cons

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceLoops
open HalfspaceGeometry HalfspaceModule ValuationModule
variable {E L X : Type} [Group E] [AddCommGroup L]
variable (π : E →* Multiplicative L)
variable [IsMulCommutative π.ker]
omit [IsMulCommutative ↥π.ker]
namespace Kourovka.MetabelianEnumeration.HalfspaceLoops
theorem _root_.solution (χ : L →+ ℝ) (g : X → E) (z : X × Bool) :
    height π χ (letter g z) = letterHeight (fun x => height π χ (g x)) z := by
  cases z with
  | mk x b => cases b <;> simp [letter, letterHeight]
end Kourovka.MetabelianEnumeration.HalfspaceLoops

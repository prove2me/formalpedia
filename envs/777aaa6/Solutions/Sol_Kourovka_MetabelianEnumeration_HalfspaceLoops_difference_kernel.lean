-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceLoops.difference_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:50.764331+00:00
-- url     : https://prove2.me/submissions/9eb83fc6-1e39-482a-bc84-95b113e91c88

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_inv
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_cons
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_letter
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.difference_one
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_one
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_mul
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_inv
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.evalWord_nil
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.evalWord_cons
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_letter

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceLoops
open HalfspaceGeometry HalfspaceModule ValuationModule
variable {E L X : Type} [Group E] [AddCommGroup L]
variable (π : E →* Multiplicative L)
variable [IsMulCommutative π.ker]
variable [DecidableEq L] [Module (GroupRing L) (Additive π.ker)]
variable (hact : ∀ (p : E) (n : Additive π.ker),
  conjugate π p n = shift (-(π p).toAdd) n)
include hact
omit [DecidableEq L]
namespace Kourovka.MetabelianEnumeration.HalfspaceLoops
theorem _root_.solution (u : E) (n : π.ker) :
    difference π u n.val = shift (-(π u).toAdd) (Additive.ofMul n) - Additive.ofMul n := by
  rw [← hact]
  apply Additive.toMul.injective
  apply Subtype.ext
  change ⁅u, n.val⁆ = (u * n.val * u⁻¹) / n.val
  rw [div_eq_mul_inv, commutatorElement_def]
end Kourovka.MetabelianEnumeration.HalfspaceLoops

-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceLoops.finite_of_lower_loops_laurent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:23:08.537174+00:00
-- url     : https://prove2.me/submissions/865d1173-90c7-4054-b217-699efa469805

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_inv
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_cons
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_letter
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_finite_of_lower_loops
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_laurent_single_image

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
namespace Kourovka.MetabelianEnumeration.HalfspaceLoops
theorem _root_.solution [Fintype X] [DecidableEq L]
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (hπ : Function.Surjective π) (g : X → E) :
    letI := CommutatorModule.laurentModule π hπ (MonoidHom.id (Multiplicative L))
    Module.Finite (GroupRing L) (Additive π.ker) →
    Subgroup.closure (loopSet π χ g (fun h => h ≤ 0)) = ⊤ →
    Module.Finite (nonnegativeRing χ) (Additive π.ker) := by
  letI := CommutatorModule.laurentModule π hπ (MonoidHom.id (Multiplicative L))
  intro hfinite hloops
  letI := hfinite
  apply finite_of_lower_loops π _ χ hχ hπ g hloops
  intro p n
  have h := CommutatorModule.laurent_single_image π hπ
    (MonoidHom.id (Multiplicative L)) (-(π p).toAdd) p⁻¹ (by simp) n
  apply Additive.toMul.injective
  apply Subtype.ext
  change p * n.toMul.val * p⁻¹ = _
  simpa only [inv_inv] using h.symm
end Kourovka.MetabelianEnumeration.HalfspaceLoops

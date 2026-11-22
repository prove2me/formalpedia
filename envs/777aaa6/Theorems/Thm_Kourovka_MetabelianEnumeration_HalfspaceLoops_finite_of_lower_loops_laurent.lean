-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_finite_of_lower_loops_laurent
-- name    : Kourovka.MetabelianEnumeration.HalfspaceLoops.finite_of_lower_loops_laurent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:59:49.667816+00:00
-- url     : https://prove2.me/theorems/8f9fbc39-6b02-470a-a163-852ac35366b0
-- title:
--   Halfspace Loops: finite of lower loops laurent
-- statement:
--   The preceding theorem for the actual quotient action; no compatibility
--   or module-action hypothesis is left to the caller.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L217-L233
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L217-L233

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceLoops
open HalfspaceGeometry HalfspaceModule ValuationModule
variable {E L X : Type} [Group E] [AddCommGroup L]
variable (π : E →* Multiplicative L)
variable [IsMulCommutative π.ker]

theorem Kourovka.MetabelianEnumeration.HalfspaceLoops.finite_of_lower_loops_laurent [Fintype X] [DecidableEq L]
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (hπ : Function.Surjective π) (g : X → E) :
    letI := CommutatorModule.laurentModule π hπ (MonoidHom.id (Multiplicative L))
    Module.Finite (GroupRing L) (Additive π.ker) →
    Subgroup.closure (loopSet π χ g (fun h => h ≤ 0)) = ⊤ →
    Module.Finite (nonnegativeRing χ) (Additive π.ker) := by sorry

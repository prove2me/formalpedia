-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_kernel
-- name    : Kourovka.MetabelianEnumeration.HalfspaceLoops.difference_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:59:41.650177+00:00
-- url     : https://prove2.me/theorems/c943250b-9d1e-48f3-a2cc-167ba50c8e69
-- title:
--   Halfspace Loops: difference kernel
-- statement:
--   The Halfspace Loops construction uses the difference kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L114-L120
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L114-L120

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
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

theorem Kourovka.MetabelianEnumeration.HalfspaceLoops.difference_kernel (u : E) (n : π.ker) :
    difference π u n.val = shift (-(π u).toAdd) (Additive.ofMul n) - Additive.ofMul n := by sorry

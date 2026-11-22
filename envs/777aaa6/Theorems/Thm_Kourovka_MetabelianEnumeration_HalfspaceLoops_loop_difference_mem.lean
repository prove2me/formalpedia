-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_loop_difference_mem
-- name    : Kourovka.MetabelianEnumeration.HalfspaceLoops.loop_difference_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:00:06.335158+00:00
-- url     : https://prove2.me/theorems/c6ec190f-0d40-486c-b3d9-9aafc4068c85
-- title:
--   Halfspace Loops: loop difference mem
-- statement:
--   The Halfspace Loops construction uses the loop difference mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L160-L167
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L160-L167

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

theorem Kourovka.MetabelianEnumeration.HalfspaceLoops.loop_difference_mem (χ : L →+ ℝ) (g : X → E) (u : E)
    (V : Submodule (nonnegativeRing χ) (Additive π.ker))
    (hletters : ∀ x, difference π u (g x) ∈ V) (n : π.ker)
    (hn : n ∈ loopSet π χ g (fun h => h ≤ 0)) : difference π u n.val ∈ V := by sorry

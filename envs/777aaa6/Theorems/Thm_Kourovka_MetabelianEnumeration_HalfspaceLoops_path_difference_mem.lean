-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_path_difference_mem
-- name    : Kourovka.MetabelianEnumeration.HalfspaceLoops.path_difference_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:00:01.789369+00:00
-- url     : https://prove2.me/theorems/98db3835-1b98-4ac6-a27a-5b14a74add3f
-- title:
--   Halfspace Loops: path difference mem
-- statement:
--   Expanding a commutator along a lower-halfspace word only uses
--   nonnegative-height conjugates of the finitely many letter commutators.
--   For an inverse letter the coefficient is taken at its ending vertex.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L125-L158
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L125-L158

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

theorem Kourovka.MetabelianEnumeration.HalfspaceLoops.path_difference_mem (χ : L →+ ℝ) (g : X → E) (u : E)
    (V : Submodule (nonnegativeRing χ) (Additive π.ker))
    (hletters : ∀ x, difference π u (g x) ∈ V)
    (w : List (X × Bool)) (p : E) (hp : difference π u p ∈ V)
    (hw : PathIn (letterHeight (fun x => height π χ (g x)))
      (fun h => h ≤ 0) (height π χ p) w) :
    difference π u (p * evalWord g w) ∈ V := by sorry

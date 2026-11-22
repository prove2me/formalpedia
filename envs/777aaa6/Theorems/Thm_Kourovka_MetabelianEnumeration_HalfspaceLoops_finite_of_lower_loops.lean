-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_finite_of_lower_loops
-- name    : Kourovka.MetabelianEnumeration.HalfspaceLoops.finite_of_lower_loops
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:59:56.843178+00:00
-- url     : https://prove2.me/theorems/811223c4-10e1-4921-a194-09eb03656f02
-- title:
--   Halfspace Loops: finite of lower loops
-- statement:
--   Bieri–Strebel's halfspace-loop lemma: genuine loop generation implies
--   finite generation over the corresponding valuation half-ring.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L196-L211
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L196-L211

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

theorem Kourovka.MetabelianEnumeration.HalfspaceLoops.finite_of_lower_loops [Fintype X]
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (hπ : Function.Surjective π) (g : X → E)
    [Module.Finite (GroupRing L) (Additive π.ker)]
    (hloops : Subgroup.closure (loopSet π χ g (fun h => h ≤ 0)) = ⊤) :
    Module.Finite (nonnegativeRing χ) (Additive π.ker) := by sorry

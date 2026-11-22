-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_lower_cutoff_to_zero
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.lower_cutoff_to_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:22:25.575368+00:00
-- url     : https://prove2.me/theorems/c95a96bf-07c4-4a33-a9e0-1a944bc2d429
-- title:
--   Schreier Heights: lower cutoff to zero
-- statement:
--   The Schreier Heights construction uses the lower cutoff to zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceShift.lean#L79-L115
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceShift.lean#L79-L115

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry HalfspaceLoops
open Kourovka.Schreier.Transversal
variable {X L : Type} [AddCommGroup L] [DecidableEq X]
omit [DecidableEq X]

theorem Kourovka.MetabelianEnumeration.SchreierHeights.lower_cutoff_to_zero (R : Set (FreeGroup X))
    (π : PresentedGroup R →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (μ : ℝ)
    (hgen : Subgroup.closure (loopSet π χ PresentedGroup.of (fun h => h ≤ μ)) = ⊤) :
    Subgroup.closure (loopSet π χ PresentedGroup.of (fun h => h ≤ 0)) = ⊤ := by sorry

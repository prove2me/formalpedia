-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_exists_negative_path
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.exists_negative_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:22:51.370625+00:00
-- url     : https://prove2.me/theorems/82a85e57-1f92-4c68-b707-0a9e9717bb4d
-- title:
--   Schreier Heights: exists negative path
-- statement:
--   The Schreier Heights construction uses the exists negative path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceShift.lean#L62-L76
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceShift.lean#L62-L76

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry HalfspaceLoops
open Kourovka.Schreier.Transversal
variable {X L : Type} [AddCommGroup L] [DecidableEq X]
omit [DecidableEq X]

theorem Kourovka.MetabelianEnumeration.SchreierHeights.exists_negative_path (R : Set (FreeGroup X))
    (π : PresentedGroup R →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (μ : ℝ) :
    ∃ s : List (X × Bool),
      PathIn (letterHeight (fun x => χ (π (PresentedGroup.of x)).toAdd)) (fun h => h ≤ 0) 0 s ∧
      χ (π (PresentedGroup.mk R (FreeGroup.mk s))).toAdd + μ ≤ 0 := by sorry

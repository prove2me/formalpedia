-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_negative_letter_of_nonzero
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.negative_letter_of_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:22:24.615174+00:00
-- url     : https://prove2.me/theorems/8c453450-a2d7-4364-860f-dba47ba07346
-- title:
--   Schreier Heights: negative letter of nonzero
-- statement:
--   The Schreier Heights construction uses the negative letter of nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceShift.lean#L24-L46
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceShift.lean#L24-L46

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry HalfspaceLoops
open Kourovka.Schreier.Transversal
variable {X L : Type} [AddCommGroup L] [DecidableEq X]
omit [DecidableEq X]

theorem Kourovka.MetabelianEnumeration.SchreierHeights.negative_letter_of_nonzero (R : Set (FreeGroup X))
    (π : PresentedGroup R →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (hχ : χ ≠ 0) :
    ∃ z : X × Bool,
      step (χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))) z < 0 := by sorry

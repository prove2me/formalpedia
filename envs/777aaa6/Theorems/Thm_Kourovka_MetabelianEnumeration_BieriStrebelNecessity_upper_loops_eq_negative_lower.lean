-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_BieriStrebelNecessity_upper_loops_eq_negative_lower
-- name    : Kourovka.MetabelianEnumeration.BieriStrebelNecessity.upper_loops_eq_negative_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:23:38.621112+00:00
-- url     : https://prove2.me/theorems/5fc5a71a-b525-4371-aa1b-1dfd0f7cdbc5
-- title:
--   Bieri Strebel Necessity: upper loops eq negative lower
-- statement:
--   The Bieri Strebel Necessity construction uses the upper loops eq negative lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/BieriStrebelNecessity.lean#L34-L51
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/BieriStrebelNecessity.lean#L34-L51

import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Definitions.Def_Kourovka_Halfspaces_BieriStrebelNecessity
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.BieriStrebelNecessity
open HalfspaceGeometry HalfspaceLoops SchreierHeights ValuationModule
open CommutatorModule SignedTameness
variable {X E L : Type} [Group E] [AddCommGroup L]

theorem Kourovka.MetabelianEnumeration.BieriStrebelNecessity.upper_loops_eq_negative_lower (π : E →* Multiplicative L)
    (χ : L →+ ℝ) (g : X → E) :
    loopSet π χ g (fun z => 0 ≤ z) = loopSet π (-χ) g (fun z => z ≤ 0) := by sorry

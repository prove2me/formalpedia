-- Prove2me | Theorems.Thm_Kourovka_Schreier_Transversal_rep_right_eq
-- name    : Kourovka.Schreier.Transversal.rep_right_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:41:08.713228+00:00
-- url     : https://prove2.me/theorems/047e4365-3b4b-456c-b4ff-1f6c8daf0a67
-- title:
--   Transversal: rep right eq
-- statement:
--   The Transversal construction uses the rep right eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/Transversal.lean#L42-L44
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/Transversal.lean#L42-L44

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic
import Definitions.Def_Kourovka_Schreier_Transversal
set_option autoImplicit true
open Kourovka Kourovka.Schreier
variable {X : Type*}
open Kourovka.Schreier.Transversal
variable {L : Subgroup (FreeGroup X)} (S : Transversal L)

theorem Kourovka.Schreier.Transversal.rep_right_eq {u v : FreeGroup X} (h : S.rep u = S.rep v) (w : FreeGroup X) :
    S.rep (u * w) = S.rep (v * w) := by sorry

-- Prove2me | Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
-- name    : Kourovka.Schreier.Transversal.evaluate_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:40:13.113333+00:00
-- url     : https://prove2.me/theorems/74f0821b-b7d3-4629-8aa4-a88f8edcb7df
-- title:
--   Transversal: evaluate of
-- statement:
--   The Transversal construction uses the evaluate of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/Transversal.lean#L85-L86
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/Transversal.lean#L85-L86

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic
import Definitions.Def_Kourovka_Schreier_Transversal
set_option autoImplicit true
open Kourovka Kourovka.Schreier
variable {X : Type*}
open Kourovka.Schreier.Transversal
variable {L : Subgroup (FreeGroup X)} (S : Transversal L)

theorem Kourovka.Schreier.Transversal.evaluate_of (z : S.Edge) : (S.evaluate (FreeGroup.of z)).val = S.edgeValue z := by sorry

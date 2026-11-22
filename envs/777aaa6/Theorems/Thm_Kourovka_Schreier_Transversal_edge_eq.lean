-- Prove2me | Theorems.Thm_Kourovka_Schreier_Transversal_edge_eq
-- name    : Kourovka.Schreier.Transversal.edge_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:40:55.211793+00:00
-- url     : https://prove2.me/theorems/5b84d933-b615-4a69-b170-55f963c68e39
-- title:
--   Transversal: edge eq
-- statement:
--   The Transversal construction uses the edge eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/Transversal.lean#L63-L67
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/Transversal.lean#L63-L67

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic
import Definitions.Def_Kourovka_Schreier_Transversal
set_option autoImplicit true
open Kourovka Kourovka.Schreier
variable {X : Type*}
open Kourovka.Schreier.Transversal
variable {L : Subgroup (FreeGroup X)} (S : Transversal L)

theorem Kourovka.Schreier.Transversal.edge_eq {p q : FreeGroup X} (h : S.rep p = S.rep q) (x : X) :
    S.edge p x = S.edge q x := by sorry

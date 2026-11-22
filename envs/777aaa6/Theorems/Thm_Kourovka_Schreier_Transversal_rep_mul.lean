-- Prove2me | Theorems.Thm_Kourovka_Schreier_Transversal_rep_mul
-- name    : Kourovka.Schreier.Transversal.rep_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:40:37.618188+00:00
-- url     : https://prove2.me/theorems/b89c4a00-87d6-4a70-b099-fbcbc9298808
-- title:
--   Transversal: rep mul
-- statement:
--   Replacing the initial vertex by its representative preserves the endpoint coset.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/Transversal.lean#L33-L37
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/Transversal.lean#L33-L37

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic
import Definitions.Def_Kourovka_Schreier_Transversal
set_option autoImplicit true
open Kourovka Kourovka.Schreier
variable {X : Type*}
open Kourovka.Schreier.Transversal
variable {L : Subgroup (FreeGroup X)} (S : Transversal L)

theorem Kourovka.Schreier.Transversal.rep_mul (u v : FreeGroup X) : S.rep (S.rep u * v) = S.rep (u * v) := by sorry

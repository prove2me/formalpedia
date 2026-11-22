-- Prove2me | Theorems.Thm_Kourovka_Schreier_Transversal_lift_map
-- name    : Kourovka.Schreier.Transversal.lift_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:14:26.723269+00:00
-- url     : https://prove2.me/theorems/05fc2aa2-9a48-4924-af49-1fdb772b7f83
-- title:
--   Transversal: lift map
-- statement:
--   Applying a homomorphism to edge labels commutes with path lifting.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/PathLifting.lean#L107-L114
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/PathLifting.lean#L107-L114

import Definitions.Def_Kourovka_Schreier_Transversal
import Definitions.Def_Kourovka_Schreier_PathLifting
set_option autoImplicit true
open Kourovka Kourovka.Schreier Kourovka.Schreier.Transversal
variable {X : Type*} {L : Subgroup (FreeGroup X)} (S : Transversal L)
variable {H : Type*} [Group H]

theorem Kourovka.Schreier.Transversal.lift_map {K : Type*} [Group K] (φ : H →* K) (f : S.Edge → H)
    (p w : FreeGroup X) : φ (S.lift f p w) = S.lift (fun z => φ (f z)) p w := by sorry

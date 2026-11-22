-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_cons
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:54:49.829652+00:00
-- url     : https://prove2.me/theorems/18a27385-8b4d-4063-956b-546191de0928
-- title:
--   Collection: shift List cons
-- statement:
--   The Collection construction uses the shift List cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L148-L153
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L148-L153

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_cons {k : ℕ} (v w : Lattice k) (i : Fin k) (l : List (Fin k))
    (hi : i ∉ l) : shiftList (shift v i (w i)) w l = shiftList v w (i :: l) := by sorry

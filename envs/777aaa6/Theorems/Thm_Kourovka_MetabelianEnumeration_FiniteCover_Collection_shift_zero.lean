-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shift_zero
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.shift_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:44:18.457794+00:00
-- url     : https://prove2.me/theorems/b636feba-5924-4878-ba38-3de74dbaf647
-- title:
--   Collection: shift zero
-- statement:
--   The Collection construction uses the shift zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L21-L22
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L21-L22

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.shift_zero {k : ℕ} (v : Lattice k) (i : Fin k) : shift v i 0 = v := by sorry

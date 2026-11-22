-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_blockWord_inverse
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.blockWord_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:54:57.824038+00:00
-- url     : https://prove2.me/theorems/069db610-5e46-4f40-8693-21cfd52822db
-- title:
--   Collection: block Word inverse
-- statement:
--   The Collection construction uses the block Word inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L217-L219
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L217-L219

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.blockWord_inverse {k : ℕ} (t : Fin k → G) (w : Lattice k) (l : List (Fin k)) :
    (blockWord t w l)⁻¹ = blockWord t (-w) l.reverse := by sorry

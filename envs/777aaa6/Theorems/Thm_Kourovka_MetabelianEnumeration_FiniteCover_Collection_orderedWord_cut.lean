-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_cut
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:44.496001+00:00
-- url     : https://prove2.me/theorems/0bab4a28-f64d-43b1-aaf8-a2f2e873f7cd
-- title:
--   Collection: ordered Word cut
-- statement:
--   Split an ordered word inside any chosen block. This is an exact group
--   identity, without commutativity assumptions.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L48-L82
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L48-L82

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_cut {k : ℕ} (t : Fin k → G) (v : Lattice k) (j : Fin k) (m : ℤ) :
    orderedWord t v = orderedWord t (cutLeft v j m) * orderedWord t (cutRight v j m) := by sorry

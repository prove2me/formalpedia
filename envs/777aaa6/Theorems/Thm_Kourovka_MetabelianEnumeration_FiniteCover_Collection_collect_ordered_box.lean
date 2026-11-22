-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collect_ordered_box
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.collect_ordered_box
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:30.902678+00:00
-- url     : https://prove2.me/theorems/e345bce2-afd1-4079-9a63-d8acd75d9e8a
-- title:
--   Collection: collect ordered box
-- statement:
--   The Collection construction uses the collect ordered box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L202-L212
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L202-L212

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.collect_ordered_box {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p : Fin a) (v w d : Lattice k) (hd : d ∈ B)
    (hv : ∀ i, |v i| ≤ |d i|) (hend : ∀ i, |v i + w i| ≤ |d i|) :
    conjugate (A p) (orderedWord t v * orderedWord t w) =
      conjugate (A p) (orderedWord t (v + w)) := by sorry

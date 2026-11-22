-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collect_blocks
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.collect_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:49:09.154114+00:00
-- url     : https://prove2.me/theorems/642b87fb-3790-4174-bc30-1951e25f6a95
-- title:
--   Collection: collect blocks
-- statement:
--   Collect any semi-ordered block sequence whose entire coordinate box
--   lies in the budget. The block order is arbitrary.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L165-L200
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L165-L200

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.collect_blocks {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p : Fin a) (v w : Lattice k) (l : List (Fin k)) (hl : l.Nodup)
    (d : Lattice k) (hd : d ∈ B)
    (hv : ∀ i, |v i| ≤ |d i|) (hend : ∀ i, |shiftList v w l i| ≤ |d i|) :
    conjugate (A p) (orderedWord t v * blockWord t w l) =
      conjugate (A p) (orderedWord t (shiftList v w l)) := by sorry

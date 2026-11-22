-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collection_three_points_words
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.collection_three_points_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:44.788068+00:00
-- url     : https://prove2.me/theorems/b122d6c6-9829-4d5d-9a76-ec653d74654a
-- title:
--   Collection: collection three points words
-- statement:
--   Three-point collection is invariant under replacing either word by
--   another word having the same conjugation action on the relevant generator.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L21-L38
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L21-L38

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.collection_three_points_words {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p q : Fin a) (x y : Lattice k) (hx : x ∈ B) (hy : y ∈ B) (hxy : x + y ∈ B)
    (U V : G)
    (hU : conjugate (A q) U = conjugate (A q) (orderedWord t x))
    (hV : conjugate (A p) V⁻¹ = conjugate (A p) (orderedWord t (-y))) :
    Commute (A p) (conjugate (A q) (U * V)) := by sorry

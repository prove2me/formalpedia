-- Prove2me | Definitions.Def_Kourovka_Collection_CollectionRadius
-- name    : Kourovka_Collection_CollectionRadius
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:44:44.140213+00:00
-- url     : https://prove2.me/theorems/551f7c66-d788-4063-a94e-7a4424eaa5ee
-- title:
--   Collection Radius
-- statement:
--   Definitions and structural lemmas for Collection Radius, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
def cutLeft {k : ℕ} (v : Lattice k) (j : Fin k) (m : ℤ) : Lattice k :=
  fun i => if i < j then v i else if i = j then m else 0
def cutRight {k : ℕ} (v : Lattice k) (j : Fin k) (m : ℤ) : Lattice k :=
  v - cutLeft v j m
end Kourovka.MetabelianEnumeration.FiniteCover.Collection



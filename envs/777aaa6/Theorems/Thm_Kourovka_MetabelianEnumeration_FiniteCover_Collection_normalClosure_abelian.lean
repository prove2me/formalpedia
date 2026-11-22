-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_normalClosure_abelian
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.normalClosure_abelian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:54:05.60179+00:00
-- url     : https://prove2.me/theorems/31fd0a91-2cc1-47b5-9c6d-5c0e7497243c
-- title:
--   Collection: normal Closure abelian
-- statement:
--   Infinite-radius collection: ordered commutation at every lattice
--   point suffices to make the full normal closure of the A-generators abelian.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L257-L320
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L257-L320

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.normalClosure_abelian {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hshort : ∀ p q v, Commute (A p) (conjugate (A q) (orderedWord t v)))
    (hgen : Subgroup.closure (Set.range t ∪ Set.range A) = ⊤) :
    ∀ x ∈ Subgroup.normalClosure (Set.range A),
      ∀ y ∈ Subgroup.normalClosure (Set.range A), Commute x y := by sorry

-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:44:04.664891+00:00
-- url     : https://prove2.me/theorems/0cf1d1f2-781a-4b3f-b437-32f0c883476e
-- title:
--   Collection: raise snoc last
-- statement:
--   The Collection construction uses the raise snoc last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L102-L104
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L102-L104

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last {k : ℕ} (v : Lattice k) (m : ℤ) :
    raise (Fin.snoc v m) (Fin.last k) = Fin.snoc v (m + 1) := by sorry

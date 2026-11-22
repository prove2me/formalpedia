-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_snoc_mem_of_abs_le
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.snoc_mem_of_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:54:27.514407+00:00
-- url     : https://prove2.me/theorems/0c67c445-4dc6-483d-9bc0-bb4bb3fc2311
-- title:
--   Collection: snoc mem of abs le
-- statement:
--   The Collection construction uses the snoc mem of abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L126-L131
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L126-L131

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.snoc_mem_of_abs_le {k : ℕ} {B : Set (Lattice (k + 1))} (hB : Solid B)
    {v : Lattice k} {m r : ℤ} (hv : Fin.snoc v m ∈ B) (hr : |r| ≤ |m|) :
    Fin.snoc v r ∈ B := by sorry

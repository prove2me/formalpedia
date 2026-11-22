-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_mul
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:43:55.584499+00:00
-- url     : https://prove2.me/theorems/04e3ff2c-2736-4a32-8940-05cd29bc4f77
-- title:
--   Collection: conjugate mul
-- statement:
--   The Collection construction uses the conjugate mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L24-L26
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L24-L26

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_mul (x u v : G) :
    conjugate x (u * v) = conjugate (conjugate x u) v := by sorry

-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_inv_pow_mul
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_inv_pow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:55.235516+00:00
-- url     : https://prove2.me/theorems/66c2030d-d966-4f59-93a5-16b52e14c242
-- title:
--   Collection: conjugate inv pow mul
-- statement:
--   The Collection construction uses the conjugate inv pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L57-L70
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L57-L70

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_inv_pow_mul (x t c : G) (n : ℕ)
    (h : ∀ r : ℕ, r ≤ n → Commute c (conjugate x (t⁻¹ ^ r))) :
    conjugate x ((t * c)⁻¹ ^ n) = conjugate x (t⁻¹ ^ n) := by sorry

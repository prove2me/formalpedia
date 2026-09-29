-- Prove2me | Theorems.Thm_mme_finset_enumerate_preserves_weight
-- name    : mme_finset_enumerate_preserves_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T22:51:49.443213+00:00
-- url     : https://prove2.me/theorems/b2c93aa3-40b1-445f-8340-c72c80bdc60d
-- title:
--   Lossless finite enumeration preserves a weighted sum
-- statement:
--   Every finite set $I$ admits an injective enumeration by $\operatorname{Fin}(|I|)$ whose image is exactly $I$. For any weight with values in an additive commutative monoid, reindexing along this enumeration preserves the total weighted sum exactly. This is the bookkeeping bridge from a selected finite set to a tensor family indexed by a finite ordinal.
-- source:
--   Standard finite-set enumeration and reindexing identity; used in the finite-family formulation of Duan--Wu--Zhou asymmetric hashing, arXiv:2210.10173.

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

set_option autoImplicit false

theorem mme_finset_enumerate_preserves_weight
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (I : Finset α) (weight : α → M) :
    ∃ edge : Fin I.card → α,
      Function.Injective edge ∧
      (∀ r, edge r ∈ I) ∧
      (∀ a, a ∈ I → ∃ r, edge r = a) ∧
      (∑ r, weight (edge r)) = ∑ a ∈ I, weight a := by
  sorry

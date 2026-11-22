-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_TamenessCompactness_finite_polynomial_identities
-- name    : Kourovka.MetabelianEnumeration.TamenessCompactness.finite_polynomial_identities
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:05:50.679179+00:00
-- url     : https://prove2.me/theorems/5b8185dc-ce82-48ca-8bb6-e4acf1879602
-- title:
--   Tameness Compactness: finite polynomial identities
-- statement:
--   The finite geometric extraction retains every signed polynomial identity
--   in the target group, with the literal inverse word used for negative tags.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/TamenessCompactness.lean#L57-L65
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/TamenessCompactness.lean#L57-L65

import Definitions.Def_Kourovka_Covers_FiniteCover
import Definitions.Def_Kourovka_Modules_TamenessCompactness
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.TamenessCompactness
open ConeVerifier FiniteCover

theorem Kourovka.MetabelianEnumeration.TamenessCompactness.finite_polynomial_identities {k a : ℕ} {G : Type*} [Group G]
    (t : Fin k → G) (A : Fin a → G)
    (h : ∀ x : Fin k → ℝ, x ≠ 0 → ∃ p : Polynomial k,
      (∀ i, A i = polynomialWord t (A i) p) ∧
      ∀ u ∈ polynomialSupport p, 0 < dot u x) :
    ∃ polynomials : List (Polynomial k),
      (∀ p ∈ polynomials, ∀ i, A i = polynomialWord t (A i) p) ∧
        ConeCover (polynomials.map polynomialSupport) := by sorry

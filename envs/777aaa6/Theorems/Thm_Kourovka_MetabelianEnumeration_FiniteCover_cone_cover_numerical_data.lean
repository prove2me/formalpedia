-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_cone_cover_numerical_data
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.cone_cover_numerical_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:07:38.286424+00:00
-- url     : https://prove2.me/theorems/c0c131e8-0331-42d1-8090-3652c018429e
-- title:
--   Finite Cover: cone cover numerical data
-- statement:
--   Every accepted cone cover supplies positive rational margins and a
--   rational bound for all support lengths.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverMargin.lean#L113-L134
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverMargin.lean#L113-L134

import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverMargin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection ConeVerifier TamenessCompactness

theorem Kourovka.MetabelianEnumeration.FiniteCover.cone_cover_numerical_data {k a : ℕ} (data : Datum k a) (hk : 1 ≤ k)
    (hc : ConeCover (data.polynomials.map polynomialSupport)) :
    ∃ C D : ℚ, 0 < C ∧ 1 ≤ D ∧ C ≤ D ∧
      (∀ p ∈ data.polynomials, ∀ term ∈ p.2, ‖euclidean term.1‖ ≤ (D : ℝ)) ∧
      (∀ v : Lattice k, v ≠ 0 → ∃ p ∈ data.polynomials,
        ∀ term ∈ p.2, inner ℝ (euclidean v) (euclidean term.1) ≤ -(C : ℝ) * ‖euclidean v‖) := by sorry

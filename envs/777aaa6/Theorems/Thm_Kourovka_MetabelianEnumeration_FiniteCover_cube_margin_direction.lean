-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_cube_margin_direction
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.cube_margin_direction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:49:43.13538+00:00
-- url     : https://prove2.me/theorems/856a7e48-4b42-40e0-aeec-0636966661f2
-- title:
--   Finite Cover: cube margin direction
-- statement:
--   A positive cube margin gives a homogeneous Euclidean shrinking margin.
--   The factor k uses the elementary bound of the Euclidean norm by the 1-norm.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverMargin.lean#L62-L109
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverMargin.lean#L62-L109

import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverMargin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection ConeVerifier TamenessCompactness

theorem Kourovka.MetabelianEnumeration.FiniteCover.cube_margin_direction {k a : ℕ} (data : Datum k a) (hk : 1 ≤ k)
    (ε : ℚ) (hε : 0 < ε)
    (hm : CubeMargin (data.polynomials.map polynomialSupport) ε) :
    ∀ v : Lattice k, v ≠ 0 → ∃ p ∈ data.polynomials,
      ∀ term ∈ p.2, inner ℝ (euclidean v) (euclidean term.1) ≤
        -((ε / k : ℚ) : ℝ) * ‖euclidean v‖ := by sorry

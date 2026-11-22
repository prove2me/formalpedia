-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_supportBound_norm
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.supportBound_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:49:19.416421+00:00
-- url     : https://prove2.me/theorems/1cc19be2-d84f-4cde-8a94-8ea5193ede02
-- title:
--   Finite Cover: support Bound norm
-- statement:
--   The Finite Cover construction uses the support Bound norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverMargin.lean#L40-L50
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverMargin.lean#L40-L50

import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverMargin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection ConeVerifier TamenessCompactness

theorem Kourovka.MetabelianEnumeration.FiniteCover.supportBound_norm {k a : ℕ} (data : Datum k a) :
    ∀ p ∈ data.polynomials, ∀ term ∈ p.2, ‖euclidean term.1‖ ≤ (supportBound data : ℝ) := by sorry

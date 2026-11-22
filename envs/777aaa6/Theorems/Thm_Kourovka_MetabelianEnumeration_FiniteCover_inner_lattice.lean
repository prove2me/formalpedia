-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_inner_lattice
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.inner_lattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:34.267444+00:00
-- url     : https://prove2.me/theorems/7093c02b-6a90-42a2-ba66-7a8962746112
-- title:
--   Finite Cover: inner lattice
-- statement:
--   The Finite Cover construction uses the inner lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverMargin.lean#L52-L58
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverMargin.lean#L52-L58

import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverMargin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection ConeVerifier TamenessCompactness

theorem Kourovka.MetabelianEnumeration.FiniteCover.inner_lattice {k : ℕ} (v u : Lattice k) :
    inner ℝ (euclidean v) (euclidean u) = ∑ i, (u i : ℝ) * (v i : ℝ) := by sorry

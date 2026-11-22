-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_supportBound_ge_one
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.supportBound_ge_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:49:14.754446+00:00
-- url     : https://prove2.me/theorems/e8ed0667-3ac2-49e1-9977-1ceef9a5f75a
-- title:
--   Finite Cover: support Bound ge one
-- statement:
--   The Finite Cover construction uses the support Bound ge one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverMargin.lean#L35-L38
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverMargin.lean#L35-L38

import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverMargin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection ConeVerifier TamenessCompactness

theorem Kourovka.MetabelianEnumeration.FiniteCover.supportBound_ge_one {k a : ℕ} (data : Datum k a) : 1 ≤ supportBound data := by sorry

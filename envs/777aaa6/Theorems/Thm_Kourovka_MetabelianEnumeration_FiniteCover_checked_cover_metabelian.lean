-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_checked_cover_metabelian
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.checked_cover_metabelian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:49:30.522379+00:00
-- url     : https://prove2.me/theorems/25c0c57b-0b62-4e7b-87c9-ddc4ae879994
-- title:
--   Finite Cover: checked cover metabelian
-- statement:
--   Soundness for the computable margin checker and explicit integer radius.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CertifiedCover.lean#L25-L42
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CertifiedCover.lean#L25-L42

import Definitions.Def_Kourovka_Covers_CoverSoundness
import Definitions.Def_Kourovka_Covers_CoverMargin
import Definitions.Def_Kourovka_Covers_CertifiedCover
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection ConeVerifier TamenessCompactness

theorem Kourovka.MetabelianEnumeration.FiniteCover.checked_cover_metabelian {k a : ℕ} (data : Datum k a) (hk : 1 ≤ k) (r : ℕ)
    (hr : checkMargin (data.polynomials.map polynomialSupport) ((1 / 2 : ℚ) ^ r) = true) :
    Metabelian (GroupOf data (coneRadius data r)) := by sorry

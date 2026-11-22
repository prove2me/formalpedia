-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_decode_supports
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.decode_supports
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:49:41.02472+00:00
-- url     : https://prove2.me/theorems/bcae5eef-b6ba-4bc7-8547-b2b35c0c5eb5
-- title:
--   Computable Cover Data: decode supports
-- statement:
--   The Computable Cover Data construction uses the decode supports property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L67-L72
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L67-L72

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.decode_supports (data : DatumCode) :
    ComputableCone.decodeSupports (dimension data) (supports data) =
      (decode data).polynomials.map TamenessCompactness.polynomialSupport := by sorry

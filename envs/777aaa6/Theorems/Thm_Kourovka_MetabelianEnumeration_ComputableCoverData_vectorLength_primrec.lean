-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_vectorLength_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.vectorLength_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:54.542763+00:00
-- url     : https://prove2.me/theorems/dabeca3f-a462-4bc3-8fcd-5ab7272e4fa4
-- title:
--   Computable Cover Data: vector Length primrec
-- statement:
--   The Computable Cover Data construction uses the vector Length primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L134-L137
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L134-L137

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.vectorLength_primrec : Primrec₂ vectorLength := by sorry

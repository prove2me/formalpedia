-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_supports_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.supports_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:01.46375+00:00
-- url     : https://prove2.me/theorems/eabdbc0b-a107-4105-82b4-67c884f92549
-- title:
--   Computable Cover Data: supports primrec
-- statement:
--   The Computable Cover Data construction uses the supports primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L125-L127
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L125-L127

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.supports_primrec : Primrec supports := by sorry

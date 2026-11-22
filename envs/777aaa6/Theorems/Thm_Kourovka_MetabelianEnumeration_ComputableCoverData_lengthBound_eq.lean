-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_lengthBound_eq
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.lengthBound_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:54.261265+00:00
-- url     : https://prove2.me/theorems/f00ec8ef-8595-46a0-a578-557c9a2dcbbf
-- title:
--   Computable Cover Data: length Bound eq
-- statement:
--   The Computable Cover Data construction uses the length Bound eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L86-L90
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L86-L90

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.lengthBound_eq (data : DatumCode) :
    (lengthBound data : ℚ) = supportBound (decode data) := by sorry

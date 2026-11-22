-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_radius_eq
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.radius_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:58.993756+00:00
-- url     : https://prove2.me/theorems/f7193717-a6ee-4f75-b614-9f175df5652e
-- title:
--   Computable Cover Data: radius eq
-- statement:
--   The Computable Cover Data construction uses the radius eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L115-L117
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L115-L117

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.radius_eq (data : DatumCode) (r : ℕ) : radius data r = coneRadius (decode data) r := by sorry

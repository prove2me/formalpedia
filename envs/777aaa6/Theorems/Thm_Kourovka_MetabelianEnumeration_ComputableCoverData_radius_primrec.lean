-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_radius_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.radius_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:03.277658+00:00
-- url     : https://prove2.me/theorems/7abcd52f-621c-41c7-a83b-ead5431340bc
-- title:
--   Computable Cover Data: radius primrec
-- statement:
--   The Computable Cover Data construction uses the radius primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L146-L154
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L146-L154

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.radius_primrec : Primrec₂ radius := by sorry

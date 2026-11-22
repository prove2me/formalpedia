-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_dimension_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.dimension_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:47:29.887086+00:00
-- url     : https://prove2.me/theorems/d2649801-424f-452e-b301-7b9e2d38e53a
-- title:
--   Computable Cover Data: dimension primrec
-- statement:
--   The Computable Cover Data construction uses the dimension primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L119-L120
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L119-L120

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.dimension_primrec : Primrec dimension := by sorry

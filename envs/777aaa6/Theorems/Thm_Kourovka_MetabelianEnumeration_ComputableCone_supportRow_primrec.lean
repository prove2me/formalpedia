-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_supportRow_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.supportRow_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:16.266761+00:00
-- url     : https://prove2.me/theorems/3f4c1b80-ad51-4ddb-a9ed-dcc084668df2
-- title:
--   Computable Cone: support Row primrec
-- statement:
--   The Computable Cone construction uses the support Row primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L211-L214
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L211-L214

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.supportRow_primrec : Primrec₂ supportRow := by sorry

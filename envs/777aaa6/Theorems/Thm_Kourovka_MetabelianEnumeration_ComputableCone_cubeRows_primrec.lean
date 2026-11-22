-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_cubeRows_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.cubeRows_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:18.279923+00:00
-- url     : https://prove2.me/theorems/f95f88f4-2323-4101-906d-e22ce187a9bc
-- title:
--   Computable Cone: cube Rows primrec
-- statement:
--   The Computable Cone construction uses the cube Rows primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L223-L229
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L223-L229

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.cubeRows_primrec : Primrec cubeRows := by sorry

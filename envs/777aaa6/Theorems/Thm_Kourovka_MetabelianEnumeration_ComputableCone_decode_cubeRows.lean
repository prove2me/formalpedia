-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_decode_cubeRows
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.decode_cubeRows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:51.811232+00:00
-- url     : https://prove2.me/theorems/c78f9975-d2e1-42ad-b124-a4333259aa64
-- title:
--   Computable Cone: decode cube Rows
-- statement:
--   The Computable Cone construction uses the decode cube Rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L86-L91
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L86-L91

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.decode_cubeRows (n : ℕ) :
    (cubeRows n).map (decodeRow n) = ConeVerifier.cubeRows n := by sorry

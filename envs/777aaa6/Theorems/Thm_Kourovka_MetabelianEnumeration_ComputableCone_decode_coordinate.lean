-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_decode_coordinate
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.decode_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:19.19943+00:00
-- url     : https://prove2.me/theorems/44d60250-e205-4e13-8a12-26e11fdb661d
-- title:
--   Computable Cone: decode coordinate
-- statement:
--   The Computable Cone construction uses the decode coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L78-L84
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L78-L84

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.decode_coordinate (n : ℕ) (i : Fin n) (a b : ℤ) :
    decodeRow n (coordinate n i a b) = ConeVerifier.coordinate i (a : ℚ) (b : ℚ) := by sorry

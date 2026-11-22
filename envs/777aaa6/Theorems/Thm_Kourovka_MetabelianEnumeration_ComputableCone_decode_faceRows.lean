-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_decode_faceRows
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.decode_faceRows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:51.937578+00:00
-- url     : https://prove2.me/theorems/2ddc9c0e-68b4-4f41-9589-718bd862626e
-- title:
--   Computable Cone: decode face Rows
-- statement:
--   The Computable Cone construction uses the decode face Rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L93-L96
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L93-L96

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.decode_faceRows (n : ℕ) (i : Fin n) (sign : ℤ) :
    (faceRows n i sign).map (decodeRow n) = ConeVerifier.faceRows i (sign : ℚ) := by sorry

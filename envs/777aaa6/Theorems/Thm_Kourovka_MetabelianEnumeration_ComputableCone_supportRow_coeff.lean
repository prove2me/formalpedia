-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_supportRow_coeff
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.supportRow_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:46.454364+00:00
-- url     : https://prove2.me/theorems/8abde97a-9702-4b2a-bf8e-f70ac85d4ab4
-- title:
--   Computable Cone: support Row coeff
-- statement:
--   The Computable Cone construction uses the support Row coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L52-L56
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L52-L56

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.supportRow_coeff (n r : ℕ) (v : VectorCode) (i : Fin n) :
    (decodeRow n (supportRow r v)).coeff i = (2 ^ r : ℚ) * decodeVector n v i := by sorry

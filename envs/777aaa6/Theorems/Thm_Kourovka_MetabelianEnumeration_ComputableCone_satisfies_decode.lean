-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_satisfies_decode
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.satisfies_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:56.026156+00:00
-- url     : https://prove2.me/theorems/d4a150c7-34b0-4cbd-9aaa-3ab5ae15c5ff
-- title:
--   Computable Cone: satisfies decode
-- statement:
--   The Computable Cone construction uses the satisfies decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L101-L104
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L101-L104

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.satisfies_decode (n : ℕ) (rows : List RowCode) (x : Fin n → ℝ) :
    FourierMotzkin.Satisfies (rows.map (decodeRow n)) x ↔ Satisfies n rows x := by sorry

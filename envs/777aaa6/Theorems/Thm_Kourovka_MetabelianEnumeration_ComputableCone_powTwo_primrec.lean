-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_powTwo_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.powTwo_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:18.084085+00:00
-- url     : https://prove2.me/theorems/ac6e6db2-64b4-407a-8e69-d4ccff6ba6d7
-- title:
--   Computable Cone: pow Two primrec
-- statement:
--   The Computable Cone construction uses the pow Two primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L208-L209
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L208-L209

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.powTwo_primrec : Primrec (fun r : ℕ => (2 ^ r : ℤ)) := by sorry

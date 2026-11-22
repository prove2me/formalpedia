-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_mul_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.mul_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:08.651749+00:00
-- url     : https://prove2.me/theorems/efd88bdf-4ee2-4f38-af5d-38f26cd12831
-- title:
--   Computable Integers: mul primrec
-- statement:
--   The Computable Integers construction uses the mul primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L93-L107
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L93-L107

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mul_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.mul_primrec : Primrec₂ (fun x y : ℤ => x * y) := by sorry

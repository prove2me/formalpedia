-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_sub_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.sub_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:51.13511+00:00
-- url     : https://prove2.me/theorems/ab656cda-b988-484f-bdaa-db5f329fb6d9
-- title:
--   Computable Integers: sub primrec
-- statement:
--   The Computable Integers construction uses the sub primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L74-L75
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L74-L75

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.sub_primrec : Primrec₂ (fun x y : ℤ => x - y) := by sorry

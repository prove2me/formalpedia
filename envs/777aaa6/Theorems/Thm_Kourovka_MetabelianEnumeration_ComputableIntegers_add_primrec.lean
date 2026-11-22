-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_add_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.add_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:48.837174+00:00
-- url     : https://prove2.me/theorems/53034df3-f078-4b53-bd15-aa0b0d248d82
-- title:
--   Computable Integers: add primrec
-- statement:
--   The Computable Integers construction uses the add primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L62-L72
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L62-L72

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.add_primrec : Primrec₂ (fun x y : ℤ => x + y) := by sorry

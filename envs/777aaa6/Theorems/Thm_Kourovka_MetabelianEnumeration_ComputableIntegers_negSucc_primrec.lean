-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_negSucc_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.negSucc_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:42.869237+00:00
-- url     : https://prove2.me/theorems/339203fd-4fe9-4fe1-a959-1764975ef30d
-- title:
--   Computable Integers: neg Succ primrec
-- statement:
--   The Computable Integers construction uses the neg Succ primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L22-L23
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L22-L23

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.negSucc_primrec : Primrec Int.negSucc := by sorry

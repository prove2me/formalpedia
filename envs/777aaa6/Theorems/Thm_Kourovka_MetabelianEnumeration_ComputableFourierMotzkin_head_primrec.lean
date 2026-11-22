-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_head_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.head_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:47.296235+00:00
-- url     : https://prove2.me/theorems/58d4de86-fd4a-4fc1-8625-f4ca01c635c8
-- title:
--   Computable Fourier Motzkin: head primrec
-- statement:
--   The Computable Fourier Motzkin construction uses the head primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L48-L48
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L48-L48

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.head_primrec : Primrec head := by sorry

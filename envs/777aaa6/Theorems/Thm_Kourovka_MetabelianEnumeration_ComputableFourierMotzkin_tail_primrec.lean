-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_tail_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.tail_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:37.469475+00:00
-- url     : https://prove2.me/theorems/c826996d-d30d-4bc2-a5ef-9d081531d708
-- title:
--   Computable Fourier Motzkin: tail primrec
-- statement:
--   The Computable Fourier Motzkin construction uses the tail primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L50-L50
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L50-L50

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.tail_primrec : Primrec tail := by sorry

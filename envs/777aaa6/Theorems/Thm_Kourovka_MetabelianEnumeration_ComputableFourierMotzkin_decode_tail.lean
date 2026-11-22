-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_decode_tail
-- name    : Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.decode_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:21.962842+00:00
-- url     : https://prove2.me/theorems/3e5f96af-363c-49b4-a34d-e0bb22c7f90a
-- title:
--   Computable Fourier Motzkin: decode tail
-- statement:
--   The Computable Fourier Motzkin construction uses the decode tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L92-L97
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L92-L97

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.decode_tail (n : ℕ) (r : RowCode) :
    decodeRow n (tail r) = (decodeRow (n + 1) r).tail := by sorry

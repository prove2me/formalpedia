-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_decode_combine
-- name    : Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.decode_combine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:29.044559+00:00
-- url     : https://prove2.me/theorems/4899d487-7086-4375-b2d6-ebf23b3a8c4f
-- title:
--   Computable Fourier Motzkin: decode combine
-- statement:
--   The Computable Fourier Motzkin construction uses the decode combine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L108-L114
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L108-L114

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.decode_combine (n : ℕ) (p : RowCode × RowCode) :
    decodeRow n (combine p) = (decodeRow (n + 1) p.1).combine (decodeRow (n + 1) p.2) := by sorry

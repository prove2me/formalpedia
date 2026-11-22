-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_check_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.check_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:03:20.901204+00:00
-- url     : https://prove2.me/theorems/31e91bf1-b2af-46a9-8f03-d7f528802cc6
-- title:
--   Computable Fourier Motzkin: check primrec
-- statement:
--   The Computable Fourier Motzkin construction uses the check primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L82-L88
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L82-L88

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.check_primrec : Primrec₂ check := by sorry

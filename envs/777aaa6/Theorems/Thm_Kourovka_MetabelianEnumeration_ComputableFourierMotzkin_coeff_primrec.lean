-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_coeff_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.coeff_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:47:27.133255+00:00
-- url     : https://prove2.me/theorems/ec47a444-20a0-4379-8fd7-3ce22c5b3835
-- title:
--   Computable Fourier Motzkin: coeff primrec
-- statement:
--   The Computable Fourier Motzkin construction uses the coeff primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L45-L46
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableFourierMotzkin.lean#L45-L46

import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
open ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableFourierMotzkin.coeff_primrec : Primrec₂ coeff := by sorry

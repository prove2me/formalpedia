-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_QuotientCodes_appendRelators_primrec
-- name    : Kourovka.MetabelianEnumeration.QuotientCodes.appendRelators_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:55.530076+00:00
-- url     : https://prove2.me/theorems/f9b28eaf-dcc0-4445-9b18-2666105849dd
-- title:
--   Quotient Codes: append Relators primrec
-- statement:
--   The Quotient Codes construction uses the append Relators primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/QuotientCodes.lean#L22-L24
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/QuotientCodes.lean#L22-L24

import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Definitions.Def_Kourovka_Presentations_QuotientCodes
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.QuotientCodes
open NaturalWordSubstitution WordCertificates

theorem Kourovka.MetabelianEnumeration.QuotientCodes.appendRelators_primrec : Primrec₂ appendRelators := by sorry

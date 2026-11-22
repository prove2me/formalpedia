-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_QuotientCodes_zero_generators_metabelian
-- name    : Kourovka.MetabelianEnumeration.QuotientCodes.zero_generators_metabelian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:09.42968+00:00
-- url     : https://prove2.me/theorems/665d770c-6cfc-4c68-a7ad-b82ce48ec883
-- title:
--   Quotient Codes: zero generators metabelian
-- statement:
--   The Quotient Codes construction uses the zero generators metabelian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/QuotientCodes.lean#L79-L90
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/QuotientCodes.lean#L79-L90

import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Definitions.Def_Kourovka_Presentations_QuotientCodes
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.QuotientCodes
open NaturalWordSubstitution WordCertificates

theorem Kourovka.MetabelianEnumeration.QuotientCodes.zero_generators_metabelian (p : PresentationCode) (h : p.1 = 0) :
    Metabelian (GroupOf p) := by sorry

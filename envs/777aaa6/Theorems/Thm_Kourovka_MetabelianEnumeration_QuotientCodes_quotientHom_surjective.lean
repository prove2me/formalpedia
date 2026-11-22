-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_QuotientCodes_quotientHom_surjective
-- name    : Kourovka.MetabelianEnumeration.QuotientCodes.quotientHom_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:36.071763+00:00
-- url     : https://prove2.me/theorems/e13d190b-403b-457f-89d3-f21f89a7dc8e
-- title:
--   Quotient Codes: quotient Hom surjective
-- statement:
--   The Quotient Codes construction uses the quotient Hom surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/QuotientCodes.lean#L40-L44
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/QuotientCodes.lean#L40-L44

import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Definitions.Def_Kourovka_Presentations_QuotientCodes
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.QuotientCodes
open NaturalWordSubstitution WordCertificates

theorem Kourovka.MetabelianEnumeration.QuotientCodes.quotientHom_surjective (p : PresentationCode) (extra : List (List (ℕ × Bool))) :
    Function.Surjective (quotientHom p extra) := by sorry

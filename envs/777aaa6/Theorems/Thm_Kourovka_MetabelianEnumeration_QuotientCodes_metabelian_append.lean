-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_QuotientCodes_metabelian_append
-- name    : Kourovka.MetabelianEnumeration.QuotientCodes.metabelian_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:38.029468+00:00
-- url     : https://prove2.me/theorems/e3c16dbd-1485-45b3-80a7-62edd521c2c1
-- title:
--   Quotient Codes: metabelian append
-- statement:
--   The Quotient Codes construction uses the metabelian append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/QuotientCodes.lean#L46-L48
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/QuotientCodes.lean#L46-L48

import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Definitions.Def_Kourovka_Presentations_QuotientCodes
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.QuotientCodes
open NaturalWordSubstitution WordCertificates

theorem Kourovka.MetabelianEnumeration.QuotientCodes.metabelian_append (p : PresentationCode) (extra : List (List (ℕ × Bool)))
    (h : Metabelian (GroupOf p)) : Metabelian (GroupOf (appendRelators p extra)) := by sorry

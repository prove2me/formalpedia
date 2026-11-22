-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_QuotientCodes_finite_quotient_codes
-- name    : Kourovka.MetabelianEnumeration.QuotientCodes.finite_quotient_codes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:06.771476+00:00
-- url     : https://prove2.me/theorems/9a995b3d-81ca-4dfc-9ce5-3ab677282140
-- title:
--   Quotient Codes: finite quotient codes
-- statement:
--   Every actual finite-presentation quotient has finitely many additional
--   natural-word relators on the unchanged source alphabet.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/QuotientCodes.lean#L52-L77
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/QuotientCodes.lean#L52-L77

import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Definitions.Def_Kourovka_Presentations_QuotientCodes
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.QuotientCodes
open NaturalWordSubstitution WordCertificates

theorem Kourovka.MetabelianEnumeration.QuotientCodes.finite_quotient_codes (p q : PresentationCode) (hp : WellFormed p)
    (_hq : WellFormed q) (f : GroupOf p →* GroupOf q) (hf : Function.Surjective f) :
    ∃ extra : List (List (ℕ × Bool)), WellFormed (appendRelators p extra) ∧
      Nonempty (GroupOf (appendRelators p extra) ≃* GroupOf q) := by sorry

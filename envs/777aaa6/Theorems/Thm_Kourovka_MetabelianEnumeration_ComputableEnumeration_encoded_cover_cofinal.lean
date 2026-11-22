-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_encoded_cover_cofinal
-- name    : Kourovka.MetabelianEnumeration.ComputableEnumeration.encoded_cover_cofinal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:25:29.254844+00:00
-- url     : https://prove2.me/theorems/5bce3635-c33d-41ef-bab9-18c2ec3724cc
-- title:
--   Computable Enumeration: encoded cover cofinal
-- statement:
--   Every nonzero-generator metabelian presentation is a quotient of a
--   concrete encoded cover at an accepted, finitely checked dyadic radius.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EnumerationCofinality.lean#L21-L46
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EnumerationCofinality.lean#L21-L46

import Definitions.Def_Kourovka_Enumeration_ComputableEnumeration
import Definitions.Def_Kourovka_Cofinality_Cofinality
import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEnumeration

theorem Kourovka.MetabelianEnumeration.ComputableEnumeration.encoded_cover_cofinal (p : PresentationCode) (hG : Metabelian (GroupOf p))
    (hp : p.1 ≠ 0) :
    ∃ (data : DatumCode) (r : ℕ), ComputableCoverData.check data r = true ∧
      ∃ f : FiniteCover.GroupOf (ComputableCoverData.decode data)
        (ComputableCoverData.radius data r) →* GroupOf p, Function.Surjective f := by sorry

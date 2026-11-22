-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.QuotientCodes.metabelian_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:10.785486+00:00
-- url     : https://prove2.me/submissions/631f9586-b6d7-4188-b673-8ad39a4af528

import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Theorems.Thm_Kourovka_MetabelianEnumeration_QuotientCodes_quotientHom_surjective
import Theorems.Thm_Kourovka_MetabelianEnumeration_metabelian_surjective


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.QuotientCodes
open NaturalWordSubstitution WordCertificates
namespace Kourovka.MetabelianEnumeration.QuotientCodes
theorem _root_.solution (p : PresentationCode) (extra : List (List (ℕ × Bool)))
    (h : Metabelian (GroupOf p)) : Metabelian (GroupOf (appendRelators p extra)) :=
  metabelian_surjective (quotientHom p extra) (quotientHom_surjective p extra) h
end Kourovka.MetabelianEnumeration.QuotientCodes

-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.QuotientCodes.quotientHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:08:50.827201+00:00
-- url     : https://prove2.me/submissions/5751c8da-7c3f-4666-aff8-0bbfb0cf1c79

import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Definitions.Def_Kourovka_Presentations_QuotientCodes

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.QuotientCodes
open NaturalWordSubstitution WordCertificates
namespace Kourovka.MetabelianEnumeration.QuotientCodes
theorem _root_.solution (p : PresentationCode) (extra : List (List (ℕ × Bool))) :
    Function.Surjective (quotientHom p extra) := by
  intro x
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective (relations (appendRelators p extra)) x
  exact ⟨PresentedGroup.mk (relations p) w, rfl⟩
end Kourovka.MetabelianEnumeration.QuotientCodes

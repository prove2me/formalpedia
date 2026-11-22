-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.isomorphism_certificate_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:31.561895+00:00
-- url     : https://prove2.me/submissions/e95fa36a-61a1-4384-a9bb-d3fcfb437d50

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_MapsCertificate_sound
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_MapsCertificate_complete

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
theorem _root_.solution {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) :
    (∃ cert : MapsCertificate source target, cert.check = true) ↔
      Nonempty (PresentedGroup (relSet source) ≃* PresentedGroup (relSet target)) := by
  constructor
  · rintro ⟨cert, hcert⟩
    exact cert.sound hcert
  · rintro ⟨e⟩
    exact MapsCertificate.complete source target e
end Kourovka.MetabelianEnumeration.WordCertificates

-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.checkIso_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:06:35.750811+00:00
-- url     : https://prove2.me/submissions/2bf649a5-5860-44a3-b35d-230888d59818

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_good_obligations
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_goodMaps_sound
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_length
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_interpret_encodeImages_getD
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_goodMaps_complete
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkData_correct

attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution (pq : PresentationCode × PresentationCode) :
    (∃ n, checkIso pq n = true) ↔
      WellFormed pq.1 ∧ WellFormed pq.2 ∧ Nonempty (GroupOf pq.1 ≃* GroupOf pq.2) := by
  constructor
  · rintro ⟨n, hn⟩
    let c := decodeCertificate n
    have hd : checkData pq c = true := hn
    have h := (checkData_correct pq c.1).mp ⟨c.2, hd⟩
    exact ⟨h.1.1, h.1.2.1, goodMaps_sound pq c.1 h.1 ((good_obligations pq c.1).mp h.2)⟩
  · rintro ⟨hp, hq, ⟨e⟩⟩
    obtain ⟨fg, hv, hg⟩ := goodMaps_complete pq.1 pq.2 hp hq e
    obtain ⟨cs, hcs⟩ := (checkData_correct pq fg).mpr ⟨hv, (good_obligations pq fg).mpr hg⟩
    refine ⟨Encodable.encode (fg, cs), ?_⟩
    simpa only [checkIso, decodeCertificate, Encodable.encodek, Option.getD_some] using hcs
end Kourovka.MetabelianEnumeration.ComputableIsomorphism

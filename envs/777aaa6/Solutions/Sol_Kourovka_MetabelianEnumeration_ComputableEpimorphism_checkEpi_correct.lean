-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableEpimorphism.checkEpi_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:08:31.53822+00:00
-- url     : https://prove2.me/submissions/30708648-71af-4fcb-951a-9c0ea3c5c3c9

import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_good_obligations
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_goodMaps_sound
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_goodMaps_complete
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_checkData_correct
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkData_correct
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_length
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_wellFormed
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_eval_substitute
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_goodMaps_complete
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_goodMaps_sound
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_good_obligations
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_interpret_encodeImages_getD
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD



set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
open ComputableIsomorphism (eval_substitute encodeImages encodeImages_length
  encodeImages_wellFormed interpret_encodeImages_getD)
namespace Kourovka.MetabelianEnumeration.ComputableEpimorphism
theorem _root_.solution (pq : PresentationCode × PresentationCode) :
    (∃ n, checkEpi pq n = true) ↔
      WellFormed pq.1 ∧ WellFormed pq.2 ∧
        ∃ F : GroupOf pq.1 →* GroupOf pq.2, Function.Surjective F := by
  constructor
  · rintro ⟨n, hn⟩
    let c := decodeCertificate n
    have hd : checkData pq c = true := hn
    have h := (checkData_correct pq c.1).mp ⟨c.2, hd⟩
    exact ⟨h.1.1, h.1.2.1, goodMaps_sound pq c.1 h.1 ((good_obligations pq c.1).mp h.2)⟩
  · rintro ⟨hp, hq, e, he⟩
    obtain ⟨fg, hv, hg⟩ := goodMaps_complete pq.1 pq.2 hp hq e he
    obtain ⟨cs, hcs⟩ := (checkData_correct pq fg).mpr ⟨hv, (good_obligations pq fg).mpr hg⟩
    refine ⟨Encodable.encode (fg, cs), ?_⟩
    simpa only [checkEpi, decodeCertificate, Encodable.encodek, Option.getD_some] using hcs
end Kourovka.MetabelianEnumeration.ComputableEpimorphism

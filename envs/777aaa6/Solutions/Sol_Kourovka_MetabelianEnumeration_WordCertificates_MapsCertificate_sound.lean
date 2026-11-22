-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.MapsCertificate.sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:02.971007+00:00
-- url     : https://prove2.me/submissions/4d149fb4-657f-48f1-be14-97cafef13a2d

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_exists_iso_of_maps
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_Derivation_eval_mem


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
namespace MapsCertificate
theorem _root_.solution {n m : ℕ} {source : List (FreeGroup (Fin n))}
    {target : List (FreeGroup (Fin m))} (cert : MapsCertificate source target)
    (h : cert.check = true) :
    Nonempty (PresentedGroup (relSet source) ≃* PresentedGroup (relSet target)) := by
  have hc := of_decide_eq_true h
  obtain ⟨hs, ht, hsi, hti⟩ := hc
  apply exists_iso_of_maps source target (fun i => FreeGroup.mk (cert.forward i))
    (fun i => FreeGroup.mk (cert.backward i))
  · intro r hr
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hr
    simpa only [MapsCertificate.forwardMap, hs, List.get_eq_getElem] using
      (cert.sourceProof i).eval_mem target
  · intro r hr
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hr
    simpa only [MapsCertificate.backwardMap, ht, List.get_eq_getElem] using
      (cert.targetProof i).eval_mem source
  · intro i
    simpa only [hsi, MapsCertificate.backwardMap] using (cert.sourceInverse i).eval_mem source
  · intro i
    simpa only [hti, MapsCertificate.forwardMap] using (cert.targetInverse i).eval_mem target
end MapsCertificate
end Kourovka.MetabelianEnumeration.WordCertificates

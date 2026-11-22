-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.goodMaps_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:11.0816+00:00
-- url     : https://prove2.me/submissions/733ca0e6-647f-46dc-b73d-57c3b83ab6db

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_inverseCheck
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_substitute
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_exists_iso_of_maps


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution (pq : PresentationCode × PresentationCode) (fg : Maps)
    (hv : validMaps (pq, fg)) (hg : GoodMaps pq fg) :
    Nonempty (GroupOf pq.1 ≃* GroupOf pq.2) := by
  rcases hv with ⟨hp, hq, _, _, hfvalid, hgvalid⟩
  rcases hg with ⟨hforward, hback, hgf, hfg⟩
  apply WordCertificates.exists_iso_of_maps
    (pq.1.2.map (interpretWord pq.1.1)) (pq.2.2.map (interpretWord pq.2.1))
    (fun i => interpretWord pq.2.1 (fg.1.getD i.val []))
    (fun i => interpretWord pq.1.1 (fg.2.getD i.val []))
  · intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [← interpret_substitute pq.1.1 pq.2.1 fg.1 w (hp w hw)]
    exact (hforward w hw).2
  · intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [← interpret_substitute pq.2.1 pq.1.1 fg.2 w (hq w hw)]
    exact (hback w hw).2
  · intro i
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [← interpret_inverseCheck pq.1.1 pq.2.1 fg.1 fg.2 hfvalid i.val i.isLt]
    exact (hgf i.val i.isLt).2
  · intro i
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [← interpret_inverseCheck pq.2.1 pq.1.1 fg.2 fg.1 hgvalid i.val i.isLt]
    exact (hfg i.val i.isLt).2
end Kourovka.MetabelianEnumeration.ComputableIsomorphism

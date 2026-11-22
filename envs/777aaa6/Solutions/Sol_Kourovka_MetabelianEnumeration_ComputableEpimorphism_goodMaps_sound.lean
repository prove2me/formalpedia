-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableEpimorphism.goodMaps_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:04.286097+00:00
-- url     : https://prove2.me/submissions/8cfa3ffa-e347-42b9-b6f3-8ab5a6efbf3f

import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_exists_epi_of_maps
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_length
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_wellFormed
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_eval_substitute
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_interpret_encodeImages_getD
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_inverseCheck
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_substitute
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD



set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
open ComputableIsomorphism (eval_substitute encodeImages encodeImages_length
  encodeImages_wellFormed interpret_encodeImages_getD)
namespace Kourovka.MetabelianEnumeration.ComputableEpimorphism
theorem _root_.solution (pq : PresentationCode × PresentationCode) (fg : Maps)
    (hv : validMaps (pq, fg)) (hg : GoodMaps pq fg) :
    ∃ F : GroupOf pq.1 →* GroupOf pq.2, Function.Surjective F := by
  rcases hv with ⟨hp, _, _, _, _, hgvalid⟩
  rcases hg with ⟨hforward, hfg⟩
  apply WordCertificates.exists_epi_of_maps
    (pq.1.2.map (interpretWord pq.1.1)) (pq.2.2.map (interpretWord pq.2.1))
    (fun i => interpretWord pq.2.1 (fg.1.getD i.val []))
    (fun i => interpretWord pq.1.1 (fg.2.getD i.val []))
  · intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [← interpret_substitute pq.1.1 pq.2.1 fg.1 w (hp w hw)]
    exact (hforward w hw).2
  · intro i
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [← interpret_inverseCheck pq.2.1 pq.1.1 fg.2 fg.1 hgvalid i.val i.isLt]
    exact (hfg i.val i.isLt).2
end Kourovka.MetabelianEnumeration.ComputableEpimorphism

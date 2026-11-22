-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableEpimorphism.good_obligations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:38.208927+00:00
-- url     : https://prove2.me/submissions/b9f5f2ac-07b1-4fe5-9225-0ce703b34fb5

import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_length
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_wellFormed
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_eval_substitute
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_interpret_encodeImages_getD
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD



set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
open ComputableIsomorphism (eval_substitute encodeImages encodeImages_length
  encodeImages_wellFormed interpret_encodeImages_getD)
namespace Kourovka.MetabelianEnumeration.ComputableEpimorphism
theorem _root_.solution (pq : PresentationCode × PresentationCode) (fg : Maps) :
    (∀ input ∈ obligations (pq, fg), Good input) ↔ GoodMaps pq fg := by
  simp only [obligations, List.forall_mem_append, ComputableIsomorphism.relatorChecks,
    ComputableIsomorphism.inverseChecks, List.forall_mem_map, List.mem_range, GoodMaps]
end Kourovka.MetabelianEnumeration.ComputableEpimorphism

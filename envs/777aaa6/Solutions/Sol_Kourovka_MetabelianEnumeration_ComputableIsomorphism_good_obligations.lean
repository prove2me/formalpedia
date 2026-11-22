-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.good_obligations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:46:36.822+00:00
-- url     : https://prove2.me/submissions/be8b5755-5ccc-4fa2-aff8-ab610cc673cd

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution (pq : PresentationCode × PresentationCode) (fg : Maps) :
    (∀ input ∈ obligations (pq, fg), Good input) ↔ GoodMaps pq fg := by
  simp only [obligations, List.forall_mem_append, relatorChecks, inverseChecks,
    List.forall_mem_map, List.mem_range, GoodMaps, and_assoc]
end Kourovka.MetabelianEnumeration.ComputableIsomorphism

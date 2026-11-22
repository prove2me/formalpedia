-- Prove2me | Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
-- name    : Kourovka_Certificates_EpimorphismSemantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:03:33.777289+00:00
-- url     : https://prove2.me/theorems/548795cd-b232-4b2f-99d9-550ff1a99112
-- title:
--   Epimorphism Semantics
-- statement:
--   Definitions and structural lemmas for Epimorphism Semantics, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/EpimorphismSemantics.lean

import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_length
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_wellFormed
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_eval_substitute
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_interpret_encodeImages_getD
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD


set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.WordCertificates
end Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
open ComputableIsomorphism (eval_substitute encodeImages encodeImages_length
  encodeImages_wellFormed interpret_encodeImages_getD)
def GoodMaps (pq : PresentationCode × PresentationCode) (fg : Maps) : Prop :=
  (∀ w ∈ pq.1.2, Good (pq.2, substitute fg.1 w)) ∧
    (∀ i < pq.2.1, Good (pq.2, substitute fg.1 (fg.2.getD i []) ++ [(i, false)]))
end Kourovka.MetabelianEnumeration.ComputableEpimorphism



-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:47:15.706868+00:00
-- url     : https://prove2.me/submissions/f20135a4-4516-4580-92cb-81aca66287e4

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_length
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution {n m : ℕ} (f : Fin n → FreeGroup (Fin m))
    (i : Fin n) : interpretWord m ((encodeImages f).getD i.val []) = f i := by
  rw [List.getD_eq_getElem _ _ (by simp [encodeImages])]
  simp [encodeImages, WordCertificates.interpret_encodeWord, FreeGroup.mk_toWord]
end Kourovka.MetabelianEnumeration.ComputableIsomorphism

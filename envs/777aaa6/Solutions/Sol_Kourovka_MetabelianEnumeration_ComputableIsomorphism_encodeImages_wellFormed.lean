-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_wellFormed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:25.789191+00:00
-- url     : https://prove2.me/submissions/8b2588b9-9c36-42d1-8951-aa53ce5eb4d1

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_valid_encode


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution {n m : ℕ} (f : Fin n → FreeGroup (Fin m)) :
    WellFormed (m, encodeImages f) := by
  intro w hw
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
  exact valid_encode _
end Kourovka.MetabelianEnumeration.ComputableIsomorphism

-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:45:45.862988+00:00
-- url     : https://prove2.me/submissions/ba3967cb-7435-4333-b6ad-226383607b81

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution {n m : ℕ} (f : Fin n → FreeGroup (Fin m)) :
    (encodeImages f).length = n := by simp [encodeImages]
end Kourovka.MetabelianEnumeration.ComputableIsomorphism

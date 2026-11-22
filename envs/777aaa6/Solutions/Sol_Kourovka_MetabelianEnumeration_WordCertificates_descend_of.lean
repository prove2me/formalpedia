-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.descend_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:22.990183+00:00
-- url     : https://prove2.me/submissions/1b1202ca-c6b1-4cf4-9d27-394924467155

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
theorem _root_.solution {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) (f : Fin n → FreeGroup (Fin m))
    (h : ∀ r ∈ source, FreeGroup.lift f r ∈ Subgroup.normalClosure (relSet target))
    (i : Fin n) : descend source target f h (PresentedGroup.of i) =
      PresentedGroup.mk (relSet target) (f i) := by
  exact PresentedGroup.toGroup.of _
end Kourovka.MetabelianEnumeration.WordCertificates

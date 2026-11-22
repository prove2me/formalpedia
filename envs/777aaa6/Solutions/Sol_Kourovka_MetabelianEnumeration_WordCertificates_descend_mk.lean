-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.descend_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:51:02.754414+00:00
-- url     : https://prove2.me/submissions/704accc8-8d7d-457c-a4ca-af70a5acc5af

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
theorem _root_.solution {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) (f : Fin n → FreeGroup (Fin m))
    (h : ∀ r ∈ source, FreeGroup.lift f r ∈ Subgroup.normalClosure (relSet target))
    (w : FreeGroup (Fin n)) :
    descend source target f h (PresentedGroup.mk (relSet source) w) =
      PresentedGroup.mk (relSet target) (FreeGroup.lift f w) := by
  change FreeGroup.lift (fun i => PresentedGroup.mk (relSet target) (f i)) w = _
  exact lift_mapped_mk target f w
end Kourovka.MetabelianEnumeration.WordCertificates

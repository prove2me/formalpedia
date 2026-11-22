-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.mk_lift_of_generator_images
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:51:08.272218+00:00
-- url     : https://prove2.me/submissions/c78ec8f3-0ed8-4271-9a83-847126c885e7

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
theorem _root_.solution {n m : ℕ}
    (source : List (FreeGroup (Fin n))) (target : List (FreeGroup (Fin m)))
    (e : PresentedGroup (relSet source) →* PresentedGroup (relSet target))
    (f : Fin n → FreeGroup (Fin m))
    (hf : ∀ i, PresentedGroup.mk (relSet target) (f i) = e (PresentedGroup.of i))
    (w : FreeGroup (Fin n)) :
    PresentedGroup.mk (relSet target) (FreeGroup.lift f w) =
      e (PresentedGroup.mk (relSet source) w) := by
  have h : (PresentedGroup.mk (relSet target)).comp (FreeGroup.lift f) =
      e.comp (PresentedGroup.mk (relSet source)) := by
    apply FreeGroup.ext_hom
    intro i
    simpa only [MonoidHom.comp_apply, FreeGroup.lift_apply_of] using hf i
  exact DFunLike.congr_fun h w
end Kourovka.MetabelianEnumeration.WordCertificates

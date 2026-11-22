-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.eval_substitute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:22.331263+00:00
-- url     : https://prove2.me/submissions/f8f25074-3c6a-4358-857e-07104cc14ca1

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_substitute


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution (p q : PresentationCode) (e : GroupOf p →* GroupOf q)
    (f : Images)
    (hf : ∀ i : Fin p.1, PresentedGroup.mk (relations q)
      (interpretWord q.1 (f.getD i.val [])) = e (PresentedGroup.of i))
    (w : Word) (hw : ValidWord p.1 w) :
    PresentedGroup.mk (relations q) (interpretWord q.1 (substitute f w)) =
      e (PresentedGroup.mk (relations p) (interpretWord p.1 w)) := by
  rw [interpret_substitute p.1 q.1 f w hw]
  have h : (PresentedGroup.mk (relations q)).comp
      (FreeGroup.lift (fun i : Fin p.1 => interpretWord q.1 (f.getD i.val []))) =
      e.comp (PresentedGroup.mk (relations p)) := by
    apply FreeGroup.ext_hom
    intro i
    simpa only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, PresentedGroup.of] using hf i
  exact DFunLike.congr_fun h _
end Kourovka.MetabelianEnumeration.ComputableIsomorphism

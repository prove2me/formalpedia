-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_eval_substitute
-- name    : Kourovka.MetabelianEnumeration.ComputableIsomorphism.eval_substitute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:21.448955+00:00
-- url     : https://prove2.me/theorems/07cfffa9-a074-44b7-9cf2-069a6c09d46d
-- title:
--   Computable Isomorphism: eval substitute
-- statement:
--   Substitution evaluates to the given homomorphism whenever its finitely
--   many generator images do.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L58-L72
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean#L58-L72

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

theorem Kourovka.MetabelianEnumeration.ComputableIsomorphism.eval_substitute (p q : PresentationCode) (e : GroupOf p →* GroupOf q)
    (f : Images)
    (hf : ∀ i : Fin p.1, PresentedGroup.mk (relations q)
      (interpretWord q.1 (f.getD i.val [])) = e (PresentedGroup.of i))
    (w : Word) (hw : ValidWord p.1 w) :
    PresentedGroup.mk (relations q) (interpretWord q.1 (substitute f w)) =
      e (PresentedGroup.mk (relations p) (interpretWord p.1 w)) := by sorry

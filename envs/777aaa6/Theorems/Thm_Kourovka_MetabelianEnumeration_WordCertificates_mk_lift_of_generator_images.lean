-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_mk_lift_of_generator_images
-- name    : Kourovka.MetabelianEnumeration.WordCertificates.mk_lift_of_generator_images
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:33.555124+00:00
-- url     : https://prove2.me/theorems/a8611ceb-e427-4037-a47c-a7210bec7daf
-- title:
--   Word Certificates: mk lift of generator images
-- statement:
--   The Word Certificates construction uses the mk lift of generator images property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/PresentationIsomorphism.lean#L131-L144
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/PresentationIsomorphism.lean#L131-L144

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates

theorem Kourovka.MetabelianEnumeration.WordCertificates.mk_lift_of_generator_images {n m : ℕ}
    (source : List (FreeGroup (Fin n))) (target : List (FreeGroup (Fin m)))
    (e : PresentedGroup (relSet source) →* PresentedGroup (relSet target))
    (f : Fin n → FreeGroup (Fin m))
    (hf : ∀ i, PresentedGroup.mk (relSet target) (f i) = e (PresentedGroup.of i))
    (w : FreeGroup (Fin n)) :
    PresentedGroup.mk (relSet target) (FreeGroup.lift f w) =
      e (PresentedGroup.mk (relSet source) w) := by sorry

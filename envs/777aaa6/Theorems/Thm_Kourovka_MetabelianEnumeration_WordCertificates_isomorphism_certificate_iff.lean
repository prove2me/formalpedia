-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_isomorphism_certificate_iff
-- name    : Kourovka.MetabelianEnumeration.WordCertificates.isomorphism_certificate_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:00:39.141178+00:00
-- url     : https://prove2.me/theorems/2eba282a-52f4-4de6-b6a6-e645b739a459
-- title:
--   Word Certificates: isomorphism certificate iff
-- statement:
--   The Word Certificates construction uses the isomorphism certificate iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/PresentationIsomorphism.lean#L194-L202
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/PresentationIsomorphism.lean#L194-L202

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates

theorem Kourovka.MetabelianEnumeration.WordCertificates.isomorphism_certificate_iff {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) :
    (∃ cert : MapsCertificate source target, cert.check = true) ↔
      Nonempty (PresentedGroup (relSet source) ≃* PresentedGroup (relSet target)) := by sorry

-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_MapsCertificate_complete
-- name    : Kourovka.MetabelianEnumeration.WordCertificates.MapsCertificate.complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:25.092344+00:00
-- url     : https://prove2.me/theorems/870cc2c3-a12d-4bf3-ac39-06b1c8c3e66a
-- title:
--   Maps Certificate: complete
-- statement:
--   Every actual isomorphism has a certificate made exclusively of finite words
--   and finite normal-closure derivations. No semantic isomorphism is stored in the data.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/PresentationIsomorphism.lean#L148-L192
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/PresentationIsomorphism.lean#L148-L192

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates

theorem Kourovka.MetabelianEnumeration.WordCertificates.MapsCertificate.complete {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m)))
    (e : PresentedGroup (relSet source) ≃* PresentedGroup (relSet target)) :
    ∃ cert : MapsCertificate source target, cert.check = true := by sorry

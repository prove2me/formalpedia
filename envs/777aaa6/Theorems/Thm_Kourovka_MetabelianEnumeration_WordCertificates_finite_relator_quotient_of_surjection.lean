-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_finite_relator_quotient_of_surjection
-- name    : Kourovka.MetabelianEnumeration.WordCertificates.finite_relator_quotient_of_surjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:36.997187+00:00
-- url     : https://prove2.me/theorems/5787f21b-15df-4975-a576-87e166fe6cac
-- title:
--   Word Certificates: finite relator quotient of surjection
-- statement:
--   The Word Certificates construction uses the finite relator quotient of surjection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/FiniteQuotient.lean#L17-L76
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/FiniteQuotient.lean#L17-L76

import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates

theorem Kourovka.MetabelianEnumeration.WordCertificates.finite_relator_quotient_of_surjection {n m : ℕ}
    (source : List (FreeGroup (Fin n))) (target : List (FreeGroup (Fin m)))
    (phi : PresentedGroup (relSet source) →* PresentedGroup (relSet target))
    (hphi : Function.Surjective phi) :
    ∃ extra : List (FreeGroup (Fin n)),
      Nonempty (PresentedGroup (relSet (source ++ extra)) ≃*
        PresentedGroup (relSet target)) := by sorry

-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_descend_mk
-- name    : Kourovka.MetabelianEnumeration.WordCertificates.descend_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:28.913783+00:00
-- url     : https://prove2.me/theorems/1c15055d-7f01-43ee-befc-a9577f05c778
-- title:
--   Word Certificates: descend mk
-- statement:
--   The Word Certificates construction uses the descend mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/PresentationIsomorphism.lean#L73-L80
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/PresentationIsomorphism.lean#L73-L80

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates

theorem Kourovka.MetabelianEnumeration.WordCertificates.descend_mk {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) (f : Fin n → FreeGroup (Fin m))
    (h : ∀ r ∈ source, FreeGroup.lift f r ∈ Subgroup.normalClosure (relSet target))
    (w : FreeGroup (Fin n)) :
    descend source target f h (PresentedGroup.mk (relSet source) w) =
      PresentedGroup.mk (relSet target) (FreeGroup.lift f w) := by sorry

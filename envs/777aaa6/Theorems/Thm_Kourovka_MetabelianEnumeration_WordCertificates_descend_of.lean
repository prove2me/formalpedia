-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_descend_of
-- name    : Kourovka.MetabelianEnumeration.WordCertificates.descend_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:15.14192+00:00
-- url     : https://prove2.me/theorems/38ea5412-350e-4d90-8d53-2cf78797e905
-- title:
--   Word Certificates: descend of
-- statement:
--   The Word Certificates construction uses the descend of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/PresentationIsomorphism.lean#L66-L71
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/PresentationIsomorphism.lean#L66-L71

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates

theorem Kourovka.MetabelianEnumeration.WordCertificates.descend_of {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) (f : Fin n → FreeGroup (Fin m))
    (h : ∀ r ∈ source, FreeGroup.lift f r ∈ Subgroup.normalClosure (relSet target))
    (i : Fin n) : descend source target f h (PresentedGroup.of i) =
      PresentedGroup.mk (relSet target) (f i) := by sorry

-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_code_metabelian_iff
-- name    : Kourovka.MetabelianEnumeration.WordCertificates.code_metabelian_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:00:43.850659+00:00
-- url     : https://prove2.me/theorems/e1770589-1507-4ea9-b7e1-c115e991f429
-- title:
--   Word Certificates: code metabelian iff
-- statement:
--   The Word Certificates construction uses the code metabelian iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/RelatorCodes.lean#L55-L61
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/RelatorCodes.lean#L55-L61

import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
import Definitions.Def_Kourovka_Presentations_RelatorCodes
set_option autoImplicit true
attribute [refl] MulEquiv.refl
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates

theorem Kourovka.MetabelianEnumeration.WordCertificates.code_metabelian_iff {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    Metabelian (Kourovka.MetabelianEnumeration.GroupOf (encodeRelators rels)) ↔
      Metabelian (PresentedGroup (relSet rels)) := by sorry

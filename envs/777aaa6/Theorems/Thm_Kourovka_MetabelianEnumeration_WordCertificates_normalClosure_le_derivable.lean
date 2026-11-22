-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_normalClosure_le_derivable
-- name    : Kourovka.MetabelianEnumeration.WordCertificates.normalClosure_le_derivable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:48.785958+00:00
-- url     : https://prove2.me/theorems/bb92bfe2-0ebd-4f7c-8a22-0ce932434235
-- title:
--   Word Certificates: normal Closure le derivable
-- statement:
--   The Word Certificates construction uses the normal Closure le derivable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/WordCertificates.lean#L67-L73
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/WordCertificates.lean#L67-L73

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Kourovka_Certificates_WordCertificates
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates

theorem Kourovka.MetabelianEnumeration.WordCertificates.normalClosure_le_derivable {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    Subgroup.normalClosure {r | r ∈ rels} ≤ derivableSubgroup rels := by sorry

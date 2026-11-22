-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_freeGroup_primrec_iff
-- name    : Kourovka.MetabelianEnumeration.ComputableWords.freeGroup_primrec_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:42:37.183104+00:00
-- url     : https://prove2.me/theorems/9e3ff7ec-4d73-4435-a9e0-82d0f4c881e7
-- title:
--   Computable Words: free Group primrec iff
-- statement:
--   The Computable Words construction uses the free Group primrec iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L94-L97
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L94-L97

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]

theorem Kourovka.MetabelianEnumeration.ComputableWords.freeGroup_primrec_iff {β : Type*} [Primcodable β] {f : β → FreeGroup α} :
    Primrec f ↔ Primrec (fun b => (f b).toWord) := by sorry

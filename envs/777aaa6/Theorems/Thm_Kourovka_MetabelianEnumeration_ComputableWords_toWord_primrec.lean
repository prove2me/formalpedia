-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_toWord_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableWords.toWord_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:42:36.346428+00:00
-- url     : https://prove2.me/theorems/4528d34f-9fda-40e5-b43c-129979015262
-- title:
--   Computable Words: to Word primrec
-- statement:
--   The Computable Words construction uses the to Word primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L91-L92
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L91-L92

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]

theorem Kourovka.MetabelianEnumeration.ComputableWords.toWord_primrec : Primrec (@FreeGroup.toWord α _) := by sorry

-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_wordEq_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableWords.wordEq_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:00:07.821854+00:00
-- url     : https://prove2.me/theorems/c6edd003-ebb4-45d1-a520-320cb8df2bc6
-- title:
--   Computable Words: word Eq primrec
-- statement:
--   The Computable Words construction uses the word Eq primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L57-L58
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L57-L58

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]

theorem Kourovka.MetabelianEnumeration.ComputableWords.wordEq_primrec : Primrec₂ (@wordEq α _) := by sorry

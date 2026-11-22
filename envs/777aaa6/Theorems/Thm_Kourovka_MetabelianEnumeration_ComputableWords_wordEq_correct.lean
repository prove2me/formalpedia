-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_wordEq_correct
-- name    : Kourovka.MetabelianEnumeration.ComputableWords.wordEq_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:00:23.375757+00:00
-- url     : https://prove2.me/theorems/3f24568a-6993-4924-9229-9cef0ef44de8
-- title:
--   Computable Words: word Eq correct
-- statement:
--   The Computable Words construction uses the word Eq correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L61-L70
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L61-L70

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]
omit [Primcodable α]

theorem Kourovka.MetabelianEnumeration.ComputableWords.wordEq_correct (left right : List (α × Bool)) :
    wordEq left right = true ↔ FreeGroup.mk left = FreeGroup.mk right := by sorry

-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mul_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableWords.mul_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:42:01.094174+00:00
-- url     : https://prove2.me/theorems/9866b0b6-c4bf-41b0-a978-f1e364016805
-- title:
--   Computable Words: mul primrec
-- statement:
--   The Computable Words construction uses the mul primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L102-L106
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L102-L106

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]

theorem Kourovka.MetabelianEnumeration.ComputableWords.mul_primrec : Primrec₂ (fun x y : FreeGroup α => x * y) := by sorry

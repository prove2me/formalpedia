-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_conjugate_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableWords.conjugate_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:07.964172+00:00
-- url     : https://prove2.me/theorems/3c78c684-5366-4af4-97e8-9c299d28f65f
-- title:
--   Computable Words: conjugate primrec
-- statement:
--   The Computable Words construction uses the conjugate primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L119-L121
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L119-L121

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]

theorem Kourovka.MetabelianEnumeration.ComputableWords.conjugate_primrec : Primrec₂ (fun g x : FreeGroup α => g * x * g⁻¹) := by sorry

-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_mk_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableWords.mk_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:44:12.504269+00:00
-- url     : https://prove2.me/theorems/3d8b25c2-7da9-4535-98e4-bd740d9641e9
-- title:
--   Computable Words: mk primrec
-- statement:
--   The Computable Words construction uses the mk primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L99-L100
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L99-L100

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]

theorem Kourovka.MetabelianEnumeration.ComputableWords.mk_primrec : Primrec (@FreeGroup.mk α) := by sorry

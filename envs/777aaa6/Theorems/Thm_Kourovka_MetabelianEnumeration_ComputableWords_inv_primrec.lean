-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_inv_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableWords.inv_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:42:15.99485+00:00
-- url     : https://prove2.me/theorems/4a4ad76c-287e-44aa-92b2-a1fee094be53
-- title:
--   Computable Words: inv primrec
-- statement:
--   The Computable Words construction uses the inv primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L115-L117
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L115-L117

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]

theorem Kourovka.MetabelianEnumeration.ComputableWords.inv_primrec : Primrec (fun x : FreeGroup α => x⁻¹) := by sorry

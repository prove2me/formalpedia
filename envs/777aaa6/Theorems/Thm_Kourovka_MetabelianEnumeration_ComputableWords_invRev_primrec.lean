-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_invRev_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableWords.invRev_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:16.540224+00:00
-- url     : https://prove2.me/theorems/6154995e-691c-4625-8b56-354f6308fb55
-- title:
--   Computable Words: inv Rev primrec
-- statement:
--   The Computable Words construction uses the inv Rev primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L109-L113
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean#L109-L113

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Computability_ComputableWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]
omit [DecidableEq α]

theorem Kourovka.MetabelianEnumeration.ComputableWords.invRev_primrec : Primrec (@FreeGroup.invRev α) := by sorry

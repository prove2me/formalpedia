-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_decodeDefault_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableEnumeration.decodeDefault_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:39.585179+00:00
-- url     : https://prove2.me/theorems/7d920b47-18a6-4226-a923-6bdf00a9700d
-- title:
--   Computable Enumeration: decode Default primrec
-- statement:
--   The Computable Enumeration construction uses the decode Default primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/ComputableEnumeration.lean#L69-L71
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/ComputableEnumeration.lean#L69-L71

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Definitions.Def_Kourovka_Enumeration_ComputableEnumeration
set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEnumeration

theorem Kourovka.MetabelianEnumeration.ComputableEnumeration.decodeDefault_primrec {α : Type} [Primcodable α] (fallback : α) :
    Primrec (fun n : ℕ => (Encodable.decode (α := α) n).getD fallback) := by sorry

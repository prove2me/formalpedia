-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_designated_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.designated_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:28.472181+00:00
-- url     : https://prove2.me/theorems/feeb73dd-0f25-47f7-bd8b-e4de2803c2ef
-- title:
--   Computable Cover Words: designated primrec
-- statement:
--   The Computable Cover Words construction uses the designated primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L112-L117
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L112-L117

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.designated_primrec : Primrec (fun p : DatumCode × (ℕ × ℕ) => designated p.1 p.2.1 p.2.2) := by sorry

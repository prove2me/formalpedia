-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_prod_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.prod_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:04.532808+00:00
-- url     : https://prove2.me/theorems/52a07874-6d66-4faf-b07c-524e6d7eb8ab
-- title:
--   Computable Cover Words: prod primrec
-- statement:
--   The Computable Cover Words construction uses the prod primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L77-L81
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L77-L81

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.prod_primrec : Primrec (List.prod : List WordGroup → WordGroup) := by sorry

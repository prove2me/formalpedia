-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_tRelators_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.tRelators_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:31.748028+00:00
-- url     : https://prove2.me/theorems/ffde625d-7166-401b-bfd2-4eda45d49a91
-- title:
--   Computable Cover Words: t Relators primrec
-- statement:
--   The Computable Cover Words construction uses the t Relators primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L130-L140
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L130-L140

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.tRelators_primrec : Primrec tRelators := by sorry

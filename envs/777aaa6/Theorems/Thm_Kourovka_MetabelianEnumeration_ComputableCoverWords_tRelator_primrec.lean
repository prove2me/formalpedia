-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_tRelator_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.tRelator_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:25.935453+00:00
-- url     : https://prove2.me/theorems/19541164-679a-4b80-845b-fb0fb47d47a2
-- title:
--   Computable Cover Words: t Relator primrec
-- statement:
--   The Computable Cover Words construction uses the t Relator primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L123-L128
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L123-L128

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.tRelator_primrec : Primrec tRelator := by sorry

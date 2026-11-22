-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_shortRelator_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.shortRelator_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:26.174855+00:00
-- url     : https://prove2.me/theorems/8dac4e72-8e92-4258-804e-74611af61fd7
-- title:
--   Computable Cover Words: short Relator primrec
-- statement:
--   The Computable Cover Words construction uses the short Relator primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L147-L154
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L147-L154

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.shortRelator_primrec : Primrec shortRelator := by sorry

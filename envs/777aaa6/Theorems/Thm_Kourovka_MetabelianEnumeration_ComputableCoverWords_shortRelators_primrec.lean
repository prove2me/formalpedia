-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_shortRelators_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.shortRelators_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:05.61154+00:00
-- url     : https://prove2.me/theorems/8712c37b-9831-4200-8ef0-bad18b933cb8
-- title:
--   Computable Cover Words: short Relators primrec
-- statement:
--   The Computable Cover Words construction uses the short Relators primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L156-L172
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L156-L172

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.shortRelators_primrec : Primrec₂ shortRelators := by sorry

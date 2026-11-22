-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_ordered_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.ordered_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:14.389493+00:00
-- url     : https://prove2.me/theorems/87257f85-6ee1-4997-afaa-b50de8188631
-- title:
--   Computable Cover Words: ordered primrec
-- statement:
--   The Computable Cover Words construction uses the ordered primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L94-L97
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L94-L97

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.ordered_primrec : Primrec₂ ordered := by sorry

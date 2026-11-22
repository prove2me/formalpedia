-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_of_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.of_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:49:25.779158+00:00
-- url     : https://prove2.me/theorems/e9d0bd41-5ee0-4aff-a1f0-0f6cb6125c69
-- title:
--   Computable Cover Words: of primrec
-- statement:
--   The Computable Cover Words construction uses the of primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L54-L56
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L54-L56

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.of_primrec : Primrec (FreeGroup.of : ℕ → WordGroup) := by sorry

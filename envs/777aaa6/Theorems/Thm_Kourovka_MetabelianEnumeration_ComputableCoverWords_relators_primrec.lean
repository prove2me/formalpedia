-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_relators_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.relators_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:36.229182+00:00
-- url     : https://prove2.me/theorems/c4033740-16d0-4126-96ba-9bb61a3d7f0e
-- title:
--   Computable Cover Words: relators primrec
-- statement:
--   The Computable Cover Words construction uses the relators primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L192-L195
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L192-L195

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.relators_primrec : Primrec₂ relators := by sorry

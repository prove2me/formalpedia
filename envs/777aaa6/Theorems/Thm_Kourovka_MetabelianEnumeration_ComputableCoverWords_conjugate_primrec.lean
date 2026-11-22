-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_conjugate_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.conjugate_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:56.457824+00:00
-- url     : https://prove2.me/theorems/ec3a676b-07bb-430e-8094-17a9418c755e
-- title:
--   Computable Cover Words: conjugate primrec
-- statement:
--   The Computable Cover Words construction uses the conjugate primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L89-L92
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L89-L92

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_conjugate_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.conjugate_primrec : Primrec₂ (FiniteCover.conjugate : WordGroup → WordGroup → WordGroup) := by sorry

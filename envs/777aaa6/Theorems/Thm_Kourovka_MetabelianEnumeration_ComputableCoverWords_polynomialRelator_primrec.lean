-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_polynomialRelator_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.polynomialRelator_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:14.394907+00:00
-- url     : https://prove2.me/theorems/4468a9c4-05b4-4aa7-a762-c9999a155d87
-- title:
--   Computable Cover Words: polynomial Relator primrec
-- statement:
--   The Computable Cover Words construction uses the polynomial Relator primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L179-L186
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L179-L186

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
set_option maxHeartbeats 1000000

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.polynomialRelator_primrec : Primrec polynomialRelator := by sorry

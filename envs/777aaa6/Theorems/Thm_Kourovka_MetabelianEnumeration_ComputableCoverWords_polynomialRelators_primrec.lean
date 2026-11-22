-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_polynomialRelators_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.polynomialRelators_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:46.196014+00:00
-- url     : https://prove2.me/theorems/ca16ae8c-df2f-4359-a4f6-d1e71c042c2c
-- title:
--   Computable Cover Words: polynomial Relators primrec
-- statement:
--   The Computable Cover Words construction uses the polynomial Relators primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L188-L190
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L188-L190

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.polynomialRelators_primrec : Primrec polynomialRelators := by sorry

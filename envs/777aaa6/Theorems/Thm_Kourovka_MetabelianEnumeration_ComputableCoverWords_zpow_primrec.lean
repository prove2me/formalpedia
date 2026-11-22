-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_zpow_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.zpow_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:24.838655+00:00
-- url     : https://prove2.me/theorems/bb7e651e-549d-445a-b7de-8d39c0aa1375
-- title:
--   Computable Cover Words: zpow primrec
-- statement:
--   The Computable Cover Words construction uses the zpow primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L67-L75
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L67-L75

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.zpow_primrec : Primrec₂ (fun x : WordGroup => fun z : ℤ => x ^ z) := by sorry

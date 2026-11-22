-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_rightComm_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.rightComm_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:28.62419+00:00
-- url     : https://prove2.me/theorems/b5274660-974e-4d99-9667-f77c4379035e
-- title:
--   Computable Cover Words: right Comm primrec
-- statement:
--   The Computable Cover Words construction uses the right Comm primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L83-L87
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L83-L87

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.rightComm_primrec : Primrec₂ (FiniteCover.rightComm : WordGroup → WordGroup → WordGroup) := by sorry

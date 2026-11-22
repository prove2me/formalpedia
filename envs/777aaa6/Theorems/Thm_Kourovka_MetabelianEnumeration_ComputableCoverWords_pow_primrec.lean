-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_pow_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.pow_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:42.303331+00:00
-- url     : https://prove2.me/theorems/e6ac68bc-06cd-4aa8-ba38-360461fde4b2
-- title:
--   Computable Cover Words: pow primrec
-- statement:
--   The Computable Cover Words construction uses the pow primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L58-L65
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L58-L65

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.pow_primrec : Primrec₂ (fun x : WordGroup => fun n : ℕ => x ^ n) := by sorry

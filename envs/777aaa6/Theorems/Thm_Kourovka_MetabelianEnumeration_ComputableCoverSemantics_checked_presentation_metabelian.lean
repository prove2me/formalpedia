-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverSemantics_checked_presentation_metabelian
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverSemantics.checked_presentation_metabelian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:14:33.025406+00:00
-- url     : https://prove2.me/theorems/7995436b-e791-4878-80f2-98a2db5855d3
-- title:
--   Computable Cover Semantics: checked presentation metabelian
-- statement:
--   The Computable Cover Semantics construction uses the checked presentation metabelian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverSemantics.lean#L197-L204
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverSemantics.lean#L197-L204

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverSemantics
open ComputableCoverData ComputableCoverWords FiniteCover
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.ComputableCoverSemantics.checked_presentation_metabelian (data : DatumCode) (r : ℕ)
    (hcheck : ComputableCoverData.check data r = true) :
    Metabelian (MetabelianEnumeration.GroupOf (presentation data (radius data r))) := by sorry

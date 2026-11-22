-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverSemantics_code_generators
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverSemantics.code_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:14:52.615923+00:00
-- url     : https://prove2.me/theorems/c6fa71ba-e550-4dfc-81d2-8a677d8176b1
-- title:
--   Computable Cover Semantics: code generators
-- statement:
--   The Computable Cover Semantics construction uses the code generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverSemantics.lean#L129-L143
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverSemantics.lean#L129-L143

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverSemantics
open ComputableCoverData ComputableCoverWords FiniteCover
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.ComputableCoverSemantics.code_generators (data : DatumCode) (R : ℕ) :
    Subgroup.closure (Set.range (codeT data R) ∪ Set.range (codeA data R)) = ⊤ := by sorry

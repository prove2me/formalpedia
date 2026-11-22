-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverSemantics_codeRealizationHom_surjective
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverSemantics.codeRealizationHom_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:15:01.503187+00:00
-- url     : https://prove2.me/theorems/c6c1a1a8-3c3c-437d-8887-032dba690378
-- title:
--   Computable Cover Semantics: code Realization Hom surjective
-- statement:
--   The Computable Cover Semantics construction uses the code Realization Hom surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverSemantics.lean#L224-L236
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverSemantics.lean#L224-L236

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverSemantics
open ComputableCoverData ComputableCoverWords FiniteCover
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.ComputableCoverSemantics.codeRealizationHom_surjective (data : DatumCode) (R : ℕ)
    (t : Fin (dimension data) → G) (A : Fin (alphabet data) → G)
    (h : Realizes (decode data) R t A)
    (hgen : Subgroup.closure (Set.range t ∪ Set.range A) = ⊤) :
    Function.Surjective (codeRealizationHom data R t A h) := by sorry

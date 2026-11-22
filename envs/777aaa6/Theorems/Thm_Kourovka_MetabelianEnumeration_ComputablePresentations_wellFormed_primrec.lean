-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_wellFormed_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputablePresentations.wellFormed_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:43:21.877047+00:00
-- url     : https://prove2.me/theorems/3a6beb85-6964-4af2-aaca-daefbbca8280
-- title:
--   Computable Presentations: well Formed primrec
-- statement:
--   The Computable Presentations construction uses the well Formed primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L19-L22
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L19-L22

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords

theorem Kourovka.MetabelianEnumeration.ComputablePresentations.wellFormed_primrec : PrimrecPred WellFormed := by sorry

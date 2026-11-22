-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_coneRadius_formula
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.coneRadius_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:52.452686+00:00
-- url     : https://prove2.me/theorems/9b70ee7a-0335-4321-a939-0ed5b284dd83
-- title:
--   Computable Cover Data: cone Radius formula
-- statement:
--   The Computable Cover Data construction uses the cone Radius formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L104-L113
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L104-L113

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.coneRadius_formula {k a : ℕ} (data : FiniteCover.Datum k a) (hk : 1 ≤ k)
    (r D : ℕ) (hD : supportBound data = (D : ℚ)) :
    coneRadius data r = 1 + 2 * k * (1 + D + D ^ 2 * k * 2 ^ r) := by sorry

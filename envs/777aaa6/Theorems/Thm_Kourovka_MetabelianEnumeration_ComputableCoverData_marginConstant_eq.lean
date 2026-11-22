-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_marginConstant_eq
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.marginConstant_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:46.445036+00:00
-- url     : https://prove2.me/theorems/38babec7-6361-42ba-81c8-9594d779f1da
-- title:
--   Computable Cover Data: margin Constant eq
-- statement:
--   The Computable Cover Data construction uses the margin Constant eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L96-L102
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L96-L102

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.marginConstant_eq {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    marginConstant k r = (1 / 2 : ℚ) ^ r / k := by sorry

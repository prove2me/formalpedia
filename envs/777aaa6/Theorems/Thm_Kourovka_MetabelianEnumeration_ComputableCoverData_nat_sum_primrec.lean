-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_nat_sum_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.nat_sum_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:47:25.979707+00:00
-- url     : https://prove2.me/theorems/fd2bfe56-a53f-4fb1-9d2c-f15acc8be0f7
-- title:
--   Computable Cover Data: nat sum primrec
-- statement:
--   The Computable Cover Data construction uses the nat sum primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L129-L132
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L129-L132

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.nat_sum_primrec : Primrec (List.sum : List ℕ → ℕ) := by sorry

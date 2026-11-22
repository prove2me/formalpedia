-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_getD_ofFn
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverData.getD_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:49:34.66311+00:00
-- url     : https://prove2.me/theorems/6d0c3a3f-1d89-42e7-abc1-5e81b7045d57
-- title:
--   Computable Cover Data: get D of Fn
-- statement:
--   The Computable Cover Data construction uses the get D of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L37-L39
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean#L37-L39

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover

theorem Kourovka.MetabelianEnumeration.ComputableCoverData.getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) (i : Fin n) :
    (List.ofFn f).getD i d = f i := by sorry

-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_mem_ball_ofFn
-- name    : Kourovka.MetabelianEnumeration.ComputableLatticeBall.mem_ball_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:22.946101+00:00
-- url     : https://prove2.me/theorems/a81f62fb-94ec-4121-ba0a-7b7b975ed8cf
-- title:
--   Computable Lattice Ball: mem ball of Fn
-- statement:
--   The Computable Lattice Ball construction uses the mem ball of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L95-L103
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L95-L103

import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableLatticeBall
open ComputableIntegers ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableLatticeBall.mem_ball_ofFn {k R : ℕ} (v : Fin k → ℤ) :
    List.ofFn v ∈ ball k R ↔ (∑ i, v i ^ 2) < (R : ℤ) ^ 2 := by sorry
